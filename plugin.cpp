#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Attr.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Sema/ParsedAttr.h"
#include "clang/Sema/Sema.h"
#include "clang/Sema/SemaDiagnostic.h"
#include "llvm/IR/Attributes.h"
#include "llvm/Support/raw_ostream.h"

#include <string>

using namespace clang;

namespace
{
    struct RemoteRecordAttrInfo : public ParsedAttrInfo
    {
        static constexpr auto printInfo   = false;
        static constexpr auto prefixClass = "REMOTE_CUSTOM_";

        RemoteRecordAttrInfo()
        {
            NumArgs = 3;
            // GNU-style __attribute__(("remote_record")) and
            // C++/C2x-style
            static constexpr Spelling S[] = {
                {  ParsedAttr::AS_GNU, "remote_record"},
                {  ParsedAttr::AS_C2x, "remote_record"},
                {ParsedAttr::AS_CXX11, "remote_record"},
            };
            Spellings = S;
            IsStmt    = 1;
        }

        class Generator
        {
          public:
            class Class
            {
              public:
                Class()
                {
                }

                Class(const std::string& name)
                 : _name { prefixClass + name },
                   _original_name { name }
                {
                }

                void addBase(const std::string& base)
                {
                    _bases.push_back(base);
                }

                void addField(const std::string& templ,
                              const std::string& type,
                              const std::string& name)
                {
                    std::string field;

                    field += templ + '<' + type + "> " + name + ";\n";

                    _fields.push_back(field);
                }

                void addFieldPtr(const std::string& templ,
                                 const std::string& baseType,
                                 const std::string& name,
                                 int ptrCount)
                {
                    std::string field;

                    for (int i = 0; i < ptrCount; i++)
                    {
                        field += templ + '<';
                    }

                    field += baseType;

                    for (int i = 0; i < ptrCount; i++)
                    {
                        field += '>';
                    }

                    field += ' ' + name + ";\n";

                    _fields.push_back(field);
                }

                std::string serialize(
                  const std::string& remoteStructType) const
                {
                    std::string remoteStruct = remoteStructType + '<'
                                               + _original_name + '>';
                    std::string classStr {
                        "struct " + _name + " : public " + remoteStruct
                    };

                    for (auto&& base : _bases)
                    {
                        classStr += ", public " + base;
                    }

                    classStr += "\n{\n";

                    classStr += _name + "() = default;\n";
                    classStr += _name
                                + "(const auto rba, std::int32_t pid) : "
                                + remoteStruct + "{rba, pid}\n{}\n";

                    for (auto&& field : _fields)
                    {
                        classStr += field;
                    }

                    classStr += "};\n";

                    return classStr;
                }

                std::string name()
                {
                    return _name;
                }

              private:
                std::string _name;
                std::string _original_name;
                std::vector<std::string> _fields;
                std::vector<std::string> _bases;
            };

            static std::string serialize(
              const std::string& remoteStructType,
              const std::map<std::string, std::shared_ptr<Class>>& classes)
            {
                std::string result;

                for (auto&& cl : classes)
                {
                    result += cl.second->serialize(remoteStructType);
                }

                return result;
            }
        };

        bool diagAppertainsToDecl(Sema& S,
                                  const ParsedAttr& Attr,
                                  const Decl* D) const override
        {
            if (!isa<RecordDecl>(D))
            {
                S.Diag(Attr.getLoc(),
                       diag::warn_attribute_wrong_decl_type_str)
                  << Attr << "classes/structs/unions";
                return false;
            }
            return true;
        }

        [[nodiscard]] AttrHandling handleBase(
          Sema& S,
          RecordDecl* recordDecl,
          const ParsedAttr& Attr,
          const std::string& arg1,
          const std::string& arg2,
          std::shared_ptr<Generator::Class>& cl,
          std::map<std::string, std::shared_ptr<Generator::Class>>& classes,
          std::string spaces = "=>") const
        {
            const auto cxxRecordDecl = dyn_cast<CXXRecordDecl>(recordDecl);

            /**
             * It's a cpp class/struct ?
             * Mainly for handling bases and virtual table.
             */
            if (not cxxRecordDecl)
            {
                /**
                 * If not, then it's fine, go ahead
                 */
                return AttributeApplied;
            }

            /**
             * First process inheritance
             */
            for (auto&& base : cxxRecordDecl->bases())
            {
                const auto baseRecordDecl = base.getType()
                                              ->getAsCXXRecordDecl()
                                              ->getDefinition();
                auto attrHandling = handleDecl(S,
                                               baseRecordDecl,
                                               Attr,
                                               arg1,
                                               arg2,
                                               classes,
                                               "=" + spaces);

                cl->addBase(
                  classes[baseRecordDecl->getNameAsString()]->name());

                if (attrHandling != AttributeApplied)
                {
                    return attrHandling;
                }
            }

            /**
             * Then check for virutal functions,
             * if any exists, it's an error, for now.
             * TODO: Support vtables.
             */
            for (auto&& method : cxxRecordDecl->methods())
            {
                if (method->isVirtual())
                {
                    unsigned ID = S.getDiagnostics().getCustomDiagID(
                      DiagnosticsEngine::Error,
                      "'remote_record' "
                      "attribute "
                      "can't "
                      "work on classes "
                      "with "
                      "virtual methods");
                    S.Diag(Attr.getLoc(), ID);
                    return AttributeNotApplied;
                }
            }

            return AttributeApplied;
        }

        [[nodiscard]] AttrHandling handleFields(
          Sema& S,
          RecordDecl* recordDecl,
          const ParsedAttr& Attr,
          std::shared_ptr<Generator::Class>& cl,
          const std::string& arg1,
          const std::string& arg2,
          std::map<std::string, std::shared_ptr<Generator::Class>>& classes,
          std::string spaces = "=>") const

        {
            for (auto&& field : recordDecl->fields())
            {
                auto type = field->getType();

                /**
                 * Check if pointer type
                 */
                if (not type->isPointerType()
                    and not type->isReferenceType())
                {
                    if constexpr (printInfo)
                    {
                        llvm::errs() << spaces << ' ' << field->getName()
                                     << ' ' << type.getAsString() << '\n';
                    }

                    auto childRecordDecl = type->getAsRecordDecl();

                    if (childRecordDecl)
                    {
                        auto attrHandling = handleDecl(S,
                                                       recordDecl,
                                                       Attr,
                                                       arg1,
                                                       arg2,
                                                       classes,
                                                       spaces);

                        if (attrHandling != AttributeNotApplied)
                        {
                            return attrHandling;
                        }
                    }

                    if (childRecordDecl)
                    {
                        cl->addField(arg1,
                                     classes[type.getAsString()]->name(),
                                     field->getNameAsString());
                    }
                    else
                    {
                        cl->addField(arg1,
                                     type.getAsString(),
                                     field->getNameAsString());
                    }

                    continue;
                }

                auto baseType = type;
                int ptrCount  = 0;

                /**
                 * Count reference as pointer
                 */
                if (baseType->isReferenceType())
                {
                    baseType = baseType.getNonReferenceType();
                    ptrCount++;
                }

                while (baseType->isPointerType())
                {
                    baseType = baseType->getPointeeType();
                    ptrCount++;
                }

                auto pBaseTypeIdentifier = type.getBaseTypeIdentifier();

                /**
                 * By default it's void
                 */
                std::string baseTypeString = "void";

                if (pBaseTypeIdentifier)
                {
                    baseTypeString = pBaseTypeIdentifier->getName();
                }

                if constexpr (printInfo)
                {
                    llvm::errs()
                      << spaces << ' ' << field->getName() << " has type "
                      << type.getAsString()
                      << " has base type: " << baseTypeString << '\n';
                }

                auto childRecordDecl = baseType->getAsRecordDecl();

                if (childRecordDecl)
                {
                    auto attrHandling = handleDecl(
                      S,
                      childRecordDecl->getDefinition(),
                      Attr,
                      arg1,
                      arg2,
                      classes,
                      "=" + spaces);

                    if (attrHandling != AttributeApplied)
                    {
                        return attrHandling;
                    }
                }

                if (childRecordDecl)
                {
                    cl->addFieldPtr(arg2,
                                    classes[baseTypeString]->name(),
                                    field->getNameAsString(),
                                    ptrCount);
                }
                else
                {
                    cl->addFieldPtr(arg2,
                                    baseTypeString,
                                    field->getNameAsString(),
                                    ptrCount);
                }
            }

            return AttributeApplied;
        }

        [[nodiscard]] AttrHandling handleDecl(
          Sema& S,
          RecordDecl* recordDecl,
          const ParsedAttr& Attr,
          const std::string& arg1,
          const std::string& arg2,
          std::map<std::string, std::shared_ptr<Generator::Class>>& classes,
          std::string spaces = "=>") const
        {
            if constexpr (printInfo)
            {
                llvm::errs() << spaces << " start of "
                             << recordDecl->getName() << '\n';
            }

            auto cl = std::make_shared<Generator::Class>(
              recordDecl->getNameAsString());

            classes[recordDecl->getNameAsString()] = cl;

            auto attrHandling = handleBase(S,
                                           recordDecl,
                                           Attr,
                                           arg1,
                                           arg2,
                                           cl,
                                           classes,
                                           spaces);

            if (attrHandling != AttributeApplied)
            {
                return attrHandling;
            }

            attrHandling = handleFields(S,
                                        recordDecl,
                                        Attr,
                                        cl,
                                        arg1,
                                        arg2,
                                        classes,
                                        spaces);

            if (attrHandling != AttributeApplied)
            {
                return attrHandling;
            }

            if constexpr (printInfo)
            {
                llvm::errs() << spaces << " end of "
                             << recordDecl->getName() << '\n';
            }

            return AttributeApplied;
        }

        AttrHandling handleDeclAttribute(
          Sema& S,
          Decl* D,
          const ParsedAttr& Attr) const override
        {
            // Check if the decl is at file scope.
            if (!D->getDeclContext()->isFileContext())
            {
                unsigned ID = S.getDiagnostics().getCustomDiagID(
                  DiagnosticsEngine::Error,
                  "'remote_record' "
                  "attribute only allowed "
                  "at file "
                  "scope");
                S.Diag(Attr.getLoc(), ID);
                return AttributeNotApplied;
            }

            if (Attr.getNumArgs() != 3)
            {
                unsigned ID = S.getDiagnostics().getCustomDiagID(
                  DiagnosticsEngine::Error,
                  "'remote_record' "
                  "attribute must have 7 "
                  "arguments only");
                S.Diag(Attr.getLoc(), ID);
                return AttributeNotApplied;
            }

            const std::array<StringLiteral*, 3> args = {
                dyn_cast<StringLiteral>(Attr.getArgAsExpr(0)),
                dyn_cast<StringLiteral>(Attr.getArgAsExpr(1)),
                dyn_cast<StringLiteral>(Attr.getArgAsExpr(2)),
            };

            auto oneFailed = std::find_if(args.begin(),
                                          args.end(),
                                          [](StringLiteral* arg)
                                          {
                                              if (arg == nullptr)
                                              {
                                                  return true;
                                              }

                                              return false;
                                          });

            if (oneFailed != args.end())
            {
                unsigned ID = S.getDiagnostics().getCustomDiagID(
                  DiagnosticsEngine::Error,
                  "'remote_record' "
                  "attribute only accepts "
                  "string "
                  "literals as "
                  "arguments");
                S.Diag(Attr.getLoc(), ID);
                return AttributeNotApplied;
            }

            auto recordDecl = dyn_cast<RecordDecl>(D);

            if constexpr (printInfo)
            {
                llvm::errs() << "Applying remote_record on "
                             << recordDecl->getName() << " => " << args[0]
                             << ' ' << args[1] << ' ' << args[2] << '\n';
            }

            std::map<std::string, std::shared_ptr<Generator::Class>>
              classes;

            auto attrHandling = handleDecl(S,
                                           recordDecl->getDefinition(),
                                           Attr,
                                           args[0]->getString().str(),
                                           args[1]->getString().str(),
                                           classes,
                                           "=>");

            if (attrHandling != AttributeApplied)
            {
                return AttributeNotApplied;
            }

            llvm::errs()
              << Generator::serialize(args[2]->getString().str(),
                                      classes);
            return AttributeApplied;
        }
    };
}

static ParsedAttrInfoRegistry::Add<RemoteRecordAttrInfo> X(
  "remote_record_1337_plugin",
  "RemoteRecord 1337 "
  "remote_record");

