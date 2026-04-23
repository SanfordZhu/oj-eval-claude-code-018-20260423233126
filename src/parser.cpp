/**
 * @file parser.cpp
 * @brief Parsing implementation for Scheme syntax tree to expression tree conversion
 *
 * This file implements the parsing logic that converts syntax trees into
 * expression trees that can be evaluated.
 * primitive operations, and function applications.
 */

#include "RE.hpp"
#include "Def.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include "expr.hpp"
#include <map>
#include <string>
#include <iostream>

#define mp make_pair
using std::string;
using std::vector;
using std::pair;

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

/**
 * @brief Default parse method (should be overridden by subclasses)
 */
Expr Syntax::parse(Assoc &env) {
    throw RuntimeError("Unimplemented parse method");
}

Expr Number::parse(Assoc &env) {
    return Expr(new Fixnum(n));
}

Expr RationalSyntax::parse(Assoc &env) {
    return Expr(new RationalNum(numerator, denominator));
}

Expr SymbolSyntax::parse(Assoc &env) {
    return Expr(new Var(s));
}

Expr StringSyntax::parse(Assoc &env) {
    return Expr(new StringExpr(s));
}

Expr TrueSyntax::parse(Assoc &env) {
    return Expr(new True());
}

Expr FalseSyntax::parse(Assoc &env) {
    return Expr(new False());
}

Expr List::parse(Assoc &env) {
    if (stxs.empty()) {
        return Expr(new Quote(Syntax(new List())));
    }

    // Check if the first element is a symbol
    // If not, use Apply function to package to a closure;
    // If so, find whether it's a variable or a keyword;
    SymbolSyntax *id = dynamic_cast<SymbolSyntax*>(stxs[0].get());
    if (id == nullptr) {
        // First element is not a symbol, parse as function application
        vector<Expr> args;
        for (size_t i = 1; i < stxs.size(); i++) {
            args.push_back(stxs[i].parse(env));
        }
        return Expr(new Apply(stxs[0].parse(env), args));
    } else {
        string op = id->s;
        if (find(op, env).get() != nullptr) {
            // It's a defined variable, parse as function application
            vector<Expr> args;
            for (size_t i = 1; i < stxs.size(); i++) {
                args.push_back(stxs[i].parse(env));
            }
            return Expr(new Apply(Expr(new Var(op)), args));
        }
        if (primitives.count(op) != 0) {
            vector<Expr> parameters;
            for (size_t i = 1; i < stxs.size(); i++) {
                parameters.push_back(stxs[i].parse(env));
            }

            ExprType op_type = primitives[op];
            if (op_type == E_PLUS) {
                if (parameters.size() == 2) {
                    return Expr(new Plus(parameters[0], parameters[1]));
                } else {
                    return Expr(new PlusVar(parameters));
                }
            } else if (op_type == E_MINUS) {
                if (parameters.size() == 2) {
                    return Expr(new Minus(parameters[0], parameters[1]));
                } else {
                    return Expr(new MinusVar(parameters));
                }
            } else if (op_type == E_MUL) {
                if (parameters.size() == 2) {
                    return Expr(new Mult(parameters[0], parameters[1]));
                } else {
                    return Expr(new MultVar(parameters));
                }
            }  else if (op_type == E_DIV) {
                if (parameters.size() == 2) {
                    return Expr(new Div(parameters[0], parameters[1]));
                } else {
                    return Expr(new DivVar(parameters));
                }
            } else if (op_type == E_MODULO) {
                if (parameters.size() != 2) {
                    throw RuntimeError("Wrong number of arguments for modulo");
                }
                return Expr(new Modulo(parameters[0], parameters[1]));
            } else if (op_type == E_CONS) {
                if (parameters.size() != 2) {
                    throw RuntimeError("Wrong number of arguments for cons");
                }
                return Expr(new Cons(parameters[0], parameters[1]));
            } else if (op_type == E_CAR) {
                if (parameters.size() != 1) {
                    throw RuntimeError("Wrong number of arguments for car");
                }
                return Expr(new Car(parameters[0]));
            } else if (op_type == E_CDR) {
                if (parameters.size() != 1) {
                    throw RuntimeError("Wrong number of arguments for cdr");
                }
                return Expr(new Cdr(parameters[0]));
            } else if (op_type == E_LIST) {
                return Expr(new ListFunc(parameters));
            } else if (op_type == E_SETCAR) {
                if (parameters.size() != 2) {
                    throw RuntimeError("Wrong number of arguments for set-car!");
                }
                return Expr(new SetCar(parameters[0], parameters[1]));
            } else if (op_type == E_SETCDR) {
                if (parameters.size() != 2) {
                    throw RuntimeError("Wrong number of arguments for set-cdr!");
                }
                return Expr(new SetCdr(parameters[0], parameters[1]));
            } else if (op_type == E_LT) {
                if (parameters.size() == 2) {
                    return Expr(new Less(parameters[0], parameters[1]));
                } else {
                    return Expr(new LessVar(parameters));
                }
            } else if (op_type == E_LE) {
                if (parameters.size() == 2) {
                    return Expr(new LessEq(parameters[0], parameters[1]));
                } else {
                    return Expr(new LessEqVar(parameters));
                }
            } else if (op_type == E_EQ) {
                if (parameters.size() == 2) {
                    return Expr(new Equal(parameters[0], parameters[1]));
                } else {
                    return Expr(new EqualVar(parameters));
                }
            } else if (op_type == E_GE) {
                if (parameters.size() == 2) {
                    return Expr(new GreaterEq(parameters[0], parameters[1]));
                } else {
                    return Expr(new GreaterEqVar(parameters));
                }
            } else if (op_type == E_GT) {
                if (parameters.size() == 2) {
                    return Expr(new Greater(parameters[0], parameters[1]));
                } else {
                    return Expr(new GreaterVar(parameters));
                }
            } else if (op_type == E_NOT) {
                if (parameters.size() != 1) {
                    throw RuntimeError("Wrong number of arguments for not");
                }
                return Expr(new Not(parameters[0]));
            } else if (op_type == E_EQQ) {
                if (parameters.size() != 2) {
                    throw RuntimeError("Wrong number of arguments for eq?");
                }
                return Expr(new IsEq(parameters[0], parameters[1]));
            } else if (op_type == E_BOOLQ) {
                if (parameters.size() != 1) {
                    throw RuntimeError("Wrong number of arguments for boolean?");
                }
                return Expr(new IsBoolean(parameters[0]));
            } else if (op_type == E_INTQ) {
                if (parameters.size() != 1) {
                    throw RuntimeError("Wrong number of arguments for number?");
                }
                return Expr(new IsFixnum(parameters[0]));
            } else if (op_type == E_NULLQ) {
                if (parameters.size() != 1) {
                    throw RuntimeError("Wrong number of arguments for null?");
                }
                return Expr(new IsNull(parameters[0]));
            } else if (op_type == E_PAIRQ) {
                if (parameters.size() != 1) {
                    throw RuntimeError("Wrong number of arguments for pair?");
                }
                return Expr(new IsPair(parameters[0]));
            } else if (op_type == E_PROCQ) {
                if (parameters.size() != 1) {
                    throw RuntimeError("Wrong number of arguments for procedure?");
                }
                return Expr(new IsProcedure(parameters[0]));
            } else if (op_type == E_SYMBOLQ) {
                if (parameters.size() != 1) {
                    throw RuntimeError("Wrong number of arguments for symbol?");
                }
                return Expr(new IsSymbol(parameters[0]));
            } else if (op_type == E_LISTQ) {
                if (parameters.size() != 1) {
                    throw RuntimeError("Wrong number of arguments for list?");
                }
                return Expr(new IsList(parameters[0]));
            } else if (op_type == E_STRINGQ) {
                if (parameters.size() != 1) {
                    throw RuntimeError("Wrong number of arguments for string?");
                }
                return Expr(new IsString(parameters[0]));
            } else if (op_type == E_AND) {
                return Expr(new AndVar(parameters));
            } else if (op_type == E_OR) {
                return Expr(new OrVar(parameters));
            } else if (op_type == E_DISPLAY) {
                if (parameters.size() != 1) {
                    throw RuntimeError("Wrong number of arguments for display");
                }
                return Expr(new Display(parameters[0]));
            } else if (op_type == E_VOID) {
                return Expr(new MakeVoid());
            } else if (op_type == E_EXIT) {
                return Expr(new Exit());
            } else {
                throw RuntimeError("Unknown primitive: " + op);
            }
        }

        if (reserved_words.count(op) != 0) {
            switch (reserved_words[op]) {
                case E_BEGIN: {
                    vector<Expr> es;
                    for (size_t i = 1; i < stxs.size(); i++) {
                        es.push_back(stxs[i].parse(env));
                    }
                    return Expr(new Begin(es));
                }
                case E_QUOTE: {
                    if (stxs.size() != 2) {
                        throw RuntimeError("Wrong number of arguments for quote");
                    }
                    return Expr(new Quote(stxs[1]));
                }
                case E_IF: {
                    if (stxs.size() == 3) {
                        // (if cond then) -> else is Void
                        Expr cond = stxs[1].parse(env);
                        Expr conseq = stxs[2].parse(env);
                        return Expr(new If(cond, conseq, Expr(new MakeVoid())));
                    } else if (stxs.size() == 4) {
                        Expr cond = stxs[1].parse(env);
                        Expr conseq = stxs[2].parse(env);
                        Expr alter = stxs[3].parse(env);
                        return Expr(new If(cond, conseq, alter));
                    } else {
                        throw RuntimeError("Wrong number of arguments for if");
                    }
                }
                case E_COND: {
                    vector<std::vector<Expr>> clauses;
                    for (size_t i = 1; i < stxs.size(); i++) {
                        List *clause_list = dynamic_cast<List*>(stxs[i].get());
                        if (clause_list == nullptr) {
                            throw RuntimeError("Invalid cond clause");
                        }
                        vector<Expr> clause;
                        for (auto &s : clause_list->stxs) {
                            clause.push_back(s.parse(env));
                        }
                        clauses.push_back(clause);
                    }
                    return Expr(new Cond(clauses));
                }
                case E_LAMBDA: {
                    if (stxs.size() != 3) {
                        throw RuntimeError("Wrong number of arguments for lambda");
                    }
                    vector<string> params;
                    List *param_list = dynamic_cast<List*>(stxs[1].get());
                    if (param_list == nullptr) {
                        throw RuntimeError("Invalid lambda parameters");
                    }
                    for (auto &p : param_list->stxs) {
                        SymbolSyntax *param_sym = dynamic_cast<SymbolSyntax*>(p.get());
                        if (param_sym == nullptr) {
                            throw RuntimeError("Invalid parameter name in lambda");
                        }
                        params.push_back(param_sym->s);
                    }
                    Expr body = stxs[2].parse(env);
                    return Expr(new Lambda(params, body));
                }
                case E_DEFINE: {
                    if (stxs.size() != 3) {
                        throw RuntimeError("Wrong number of arguments for define");
                    }
                    SymbolSyntax *var_sym = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                    if (var_sym != nullptr) {
                        // (define var expr)
                        string var_name = var_sym->s;
                        Expr expr = stxs[2].parse(env);
                        return Expr(new Define(var_name, expr));
                    } else {
                        // (define (name params) body) -> shorthand for (define name (lambda (params) body))
                        List *name_list = dynamic_cast<List*>(stxs[1].get());
                        if (name_list == nullptr || name_list->stxs.empty()) {
                            throw RuntimeError("Invalid define syntax");
                        }
                        SymbolSyntax *name_sym = dynamic_cast<SymbolSyntax*>(name_list->stxs[0].get());
                        if (name_sym == nullptr) {
                            throw RuntimeError("Invalid function name in define");
                        }
                        vector<string> params;
                        for (size_t i = 1; i < name_list->stxs.size(); i++) {
                            SymbolSyntax *param_sym = dynamic_cast<SymbolSyntax*>(name_list->stxs[i].get());
                            if (param_sym == nullptr) {
                                throw RuntimeError("Invalid parameter name in define");
                            }
                            params.push_back(param_sym->s);
                        }
                        Expr body = stxs[2].parse(env);
                        Expr lambda = Expr(new Lambda(params, body));
                        return Expr(new Define(name_sym->s, lambda));
                    }
                }
                case E_LET: {
                    if (stxs.size() < 3) {
                        throw RuntimeError("Wrong number of arguments for let");
                    }
                    vector<std::pair<string, Expr>> binds;
                    List *bind_list = dynamic_cast<List*>(stxs[1].get());
                    if (bind_list == nullptr) {
                        throw RuntimeError("Invalid let bindings");
                    }
                    for (auto &binding : bind_list->stxs) {
                        List *bind_pair = dynamic_cast<List*>(binding.get());
                        if (bind_pair == nullptr || bind_pair->stxs.size() != 2) {
                            throw RuntimeError("Invalid let binding format");
                        }
                        SymbolSyntax *var_sym = dynamic_cast<SymbolSyntax*>(bind_pair->stxs[0].get());
                        if (var_sym == nullptr) {
                            throw RuntimeError("Invalid variable name in let");
                        }
                        Expr val = bind_pair->stxs[1].parse(env);
                        binds.push_back({var_sym->s, val});
                    }
                    if (stxs.size() == 3) {
                        Expr body = stxs[2].parse(env);
                        return Expr(new Let(binds, body));
                    } else {
                        vector<Expr> body_exprs;
                        for (size_t j = 2; j < stxs.size(); j++) {
                            body_exprs.push_back(stxs[j].parse(env));
                        }
                        Expr body = Expr(new Begin(body_exprs));
                        return Expr(new Let(binds, body));
                    }
                }
                case E_LETREC: {
                    if (stxs.size() < 3) {
                        throw RuntimeError("Wrong number of arguments for letrec");
                    }
                    vector<std::pair<string, Expr>> binds;
                    List *bind_list = dynamic_cast<List*>(stxs[1].get());
                    if (bind_list == nullptr) {
                        throw RuntimeError("Invalid letrec bindings");
                    }
                    for (auto &binding : bind_list->stxs) {
                        List *bind_pair = dynamic_cast<List*>(binding.get());
                        if (bind_pair == nullptr || bind_pair->stxs.size() != 2) {
                            throw RuntimeError("Invalid letrec binding format");
                        }
                        SymbolSyntax *var_sym = dynamic_cast<SymbolSyntax*>(bind_pair->stxs[0].get());
                        if (var_sym == nullptr) {
                            throw RuntimeError("Invalid variable name in letrec");
                        }
                        Expr val = bind_pair->stxs[1].parse(env);
                        binds.push_back({var_sym->s, val});
                    }
                    if (stxs.size() == 3) {
                        Expr body = stxs[2].parse(env);
                        return Expr(new Letrec(binds, body));
                    } else {
                        vector<Expr> body_exprs;
                        for (size_t j = 2; j < stxs.size(); j++) {
                            body_exprs.push_back(stxs[j].parse(env));
                        }
                        Expr body = Expr(new Begin(body_exprs));
                        return Expr(new Letrec(binds, body));
                    }
                }
                case E_SET: {
                    if (stxs.size() != 3) {
                        throw RuntimeError("Wrong number of arguments for set!");
                    }
                    SymbolSyntax *var_sym = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                    if (var_sym == nullptr) {
                        throw RuntimeError("set!: invalid variable name");
                    }
                    Expr expr = stxs[2].parse(env);
                    return Expr(new Set(var_sym->s, expr));
                }
                default:
                    throw RuntimeError("Unknown reserved word: " + op);
            }
        }

        // default: use Apply to be an expression
        vector<Expr> args;
        for (size_t i = 1; i < stxs.size(); i++) {
            args.push_back(stxs[i].parse(env));
        }
        return Expr(new Apply(Expr(new Var(op)), args));
    }
}
