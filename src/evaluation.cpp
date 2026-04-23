/**
 * @file evaluation.cpp
 * @brief Expression evaluation implementation for the Scheme interpreter
 * @author luke36
 * 
 * This file implements evaluation methods for all expression types in the Scheme
 * interpreter. Functions are organized according to ExprType enumeration order
 * from Def.hpp for consistency and maintainability.
 */

#include "value.hpp"
#include "expr.hpp" 
#include "RE.hpp"
#include "syntax.hpp"
#include <cstring>
#include <vector>
#include <map>
#include <climits>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

// Declare gcd from expr.cpp
int gcd(int a, int b);

// Helper function to create the proper result (Integer or Rational)
Value makeResult(int num, int den) {
    if (den == 1) {
        return IntegerV(num);
    }
    int g = gcd(num, den);
    num /= g;
    den /= g;
    if (den < 0) {
        num = -num;
        den = -den;
    }
    return RationalV(num, den);
}

Value Fixnum::eval(Assoc &e) { // evaluation of a fixnum
    return IntegerV(n);
}

Value RationalNum::eval(Assoc &e) { // evaluation of a rational number
    return RationalV(numerator, denominator);
}

Value StringExpr::eval(Assoc &e) { // evaluation of a string
    return StringV(s);
}

Value True::eval(Assoc &e) { // evaluation of #t
    return BooleanV(true);
}

Value False::eval(Assoc &e) { // evaluation of #f
    return BooleanV(false);
}

Value MakeVoid::eval(Assoc &e) { // (void)
    return VoidV();
}

Value Exit::eval(Assoc &e) { // (exit)
    return TerminateV();
}

Value Unary::eval(Assoc &e) { // evaluation of single-operator primitive
    return evalRator(rand->eval(e));
}

Value Binary::eval(Assoc &e) { // evaluation of two-operators primitive
    return evalRator(rand1->eval(e), rand2->eval(e));
}

Value Variadic::eval(Assoc &e) { // evaluation of multi-operator primitive
    std::vector<Value> args;
    for (auto &rand : rands) {
        args.push_back(rand->eval(e));
    }
    return evalRator(args);
}

Value Var::eval(Assoc &e) { // evaluation of variable
    // TODO: TO identify the invalid variable
    // We request all valid variable just need to be a symbol,you should promise:
    //The first character of a variable name cannot be a digit or any character from the set: {.@}
    //If a string can be recognized as a number, it will be prioritized as a number. For example: 1, -1, +123, .123, +124., 1e-3
    //Variable names can overlap with primitives and reserve_words
    //Variable names can contain any non-whitespace characters except #, ', ", `, but the first character cannot be a digit
    //When a variable is not defined in the current scope, your interpreter should output RuntimeError

    Value matched_value = find(x, e);
    if (matched_value.get() == nullptr) {
        if (primitives.count(x)) {
             static std::map<ExprType, std::pair<Expr, std::vector<std::string>>> primitive_map = {
                    {E_VOID,     {new MakeVoid(), {}}},
                    {E_EXIT,     {new Exit(), {}}},
                    {E_BOOLQ,    {new IsBoolean(new Var("parm")), {"parm"}}},
                    {E_INTQ,     {new IsFixnum(new Var("parm")), {"parm"}}},
                    {E_NULLQ,    {new IsNull(new Var("parm")), {"parm"}}},
                    {E_PAIRQ,    {new IsPair(new Var("parm")), {"parm"}}},
                    {E_PROCQ,    {new IsProcedure(new Var("parm")), {"parm"}}},
                    {E_SYMBOLQ,  {new IsSymbol(new Var("parm")), {"parm"}}},
                    {E_STRINGQ,  {new IsString(new Var("parm")), {"parm"}}},
                    {E_DISPLAY,  {new Display(new Var("parm")), {"parm"}}},
                    {E_PLUS,     {new PlusVar({}),  {}}},
                    {E_MINUS,    {new MinusVar({}), {}}},
                    {E_MUL,      {new MultVar({}),  {}}},
                    {E_DIV,      {new DivVar({}),   {}}},
                    {E_MODULO,   {new Modulo(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_EXPT,     {new Expt(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_EQQ,      {new IsEq(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
            };

            auto it = primitive_map.find(primitives[x]);
            if (it != primitive_map.end()) {
                return it->second.first->eval(e);
            }
      }
      throw RuntimeError("Undefined variable: " + x);
    }
    return matched_value;
}

Value Plus::evalRator(const Value &rand1, const Value &rand2) { // +
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(n1 + n2);
    } else {
        int num1, den1, num2, den2;
        if (rand1->v_type == V_INT) {
            num1 = dynamic_cast<Integer*>(rand1.get())->n;
            den1 = 1;
        } else if (rand1->v_type == V_RATIONAL) {
            num1 = dynamic_cast<Rational*>(rand1.get())->numerator;
            den1 = dynamic_cast<Rational*>(rand1.get())->denominator;
        } else {
            throw RuntimeError("Wrong typename in +");
        }
        if (rand2->v_type == V_INT) {
            num2 = dynamic_cast<Integer*>(rand2.get())->n;
            den2 = 1;
        } else if (rand2->v_type == V_RATIONAL) {
            num2 = dynamic_cast<Rational*>(rand2.get())->numerator;
            den2 = dynamic_cast<Rational*>(rand2.get())->denominator;
        } else {
            throw RuntimeError("Wrong typename in +");
        }
        return makeResult(num1 * den2 + num2 * den1, den1 * den2);
    }
}

Value Minus::evalRator(const Value &rand1, const Value &rand2) { // -
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(n1 - n2);
    } else {
        int num1, den1, num2, den2;
        if (rand1->v_type == V_INT) {
            num1 = dynamic_cast<Integer*>(rand1.get())->n;
            den1 = 1;
        } else if (rand1->v_type == V_RATIONAL) {
            num1 = dynamic_cast<Rational*>(rand1.get())->numerator;
            den1 = dynamic_cast<Rational*>(rand1.get())->denominator;
        } else {
            throw RuntimeError("Wrong typename in -");
        }
        if (rand2->v_type == V_INT) {
            num2 = dynamic_cast<Integer*>(rand2.get())->n;
            den2 = 1;
        } else if (rand2->v_type == V_RATIONAL) {
            num2 = dynamic_cast<Rational*>(rand2.get())->numerator;
            den2 = dynamic_cast<Rational*>(rand2.get())->denominator;
        } else {
            throw RuntimeError("Wrong typename in -");
        }
        return makeResult(num1 * den2 - num2 * den1, den1 * den2);
    }
}

Value Mult::evalRator(const Value &rand1, const Value &rand2) { // *
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(n1 * n2);
    } else {
        int num1, den1, num2, den2;
        if (rand1->v_type == V_INT) {
            num1 = dynamic_cast<Integer*>(rand1.get())->n;
            den1 = 1;
        } else if (rand1->v_type == V_RATIONAL) {
            num1 = dynamic_cast<Rational*>(rand1.get())->numerator;
            den1 = dynamic_cast<Rational*>(rand1.get())->denominator;
        } else {
            throw RuntimeError("Wrong typename in *");
        }
        if (rand2->v_type == V_INT) {
            num2 = dynamic_cast<Integer*>(rand2.get())->n;
            den2 = 1;
        } else if (rand2->v_type == V_RATIONAL) {
            num2 = dynamic_cast<Rational*>(rand2.get())->numerator;
            den2 = dynamic_cast<Rational*>(rand2.get())->denominator;
        } else {
            throw RuntimeError("Wrong typename in *");
        }
        return makeResult(num1 * num2, den1 * den2);
    }
}

Value Div::evalRator(const Value &rand1, const Value &rand2) { // /
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        if (n2 == 0) {
            throw RuntimeError("Division by zero");
        }
        return makeResult(n1, n2);
    } else {
        int num1, den1, num2, den2;
        if (rand1->v_type == V_INT) {
            num1 = dynamic_cast<Integer*>(rand1.get())->n;
            den1 = 1;
        } else if (rand1->v_type == V_RATIONAL) {
            num1 = dynamic_cast<Rational*>(rand1.get())->numerator;
            den1 = dynamic_cast<Rational*>(rand1.get())->denominator;
        } else {
            throw RuntimeError("Wrong typename in /");
        }
        if (rand2->v_type == V_INT) {
            num2 = dynamic_cast<Integer*>(rand2.get())->n;
            den2 = 1;
        } else if (rand2->v_type == V_RATIONAL) {
            num2 = dynamic_cast<Rational*>(rand2.get())->numerator;
            den2 = dynamic_cast<Rational*>(rand2.get())->denominator;
        } else {
            throw RuntimeError("Wrong typename in /");
        }
        if (num2 == 0) {
            throw RuntimeError("Division by zero");
        }
        return makeResult(num1 * den2, den1 * num2);
    }
}

Value Modulo::evalRator(const Value &rand1, const Value &rand2) { // modulo
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int dividend = dynamic_cast<Integer*>(rand1.get())->n;
        int divisor = dynamic_cast<Integer*>(rand2.get())->n;
        if (divisor == 0) {
            throw(RuntimeError("Division by zero"));
        }
        return IntegerV(dividend % divisor);
    }
    throw(RuntimeError("modulo is only defined for integers"));
}

Value PlusVar::evalRator(const std::vector<Value> &args) { // + with multiple args
    if (args.empty()) {
        return IntegerV(0);
    }
    int num = 0, den = 1;
    for (auto &arg : args) {
        if (arg->v_type == V_INT) {
            int n = dynamic_cast<Integer*>(arg.get())->n;
            num = num * 1 + n * den;
            den = den * 1;
        } else if (arg->v_type == V_RATIONAL) {
            int n = dynamic_cast<Rational*>(arg.get())->numerator;
            int d = dynamic_cast<Rational*>(arg.get())->denominator;
            num = num * d + n * den;
            den = den * d;
        } else {
            throw RuntimeError("Wrong typename in +");
        }
    }
    return makeResult(num, den);
}

Value MinusVar::evalRator(const std::vector<Value> &args) { // - with multiple args
    if (args.empty()) {
        throw RuntimeError("Wrong number of arguments for -");
    }
    if (args.size() == 1) {
        // (- x) -> -x
        if (args[0]->v_type == V_INT) {
            int n = dynamic_cast<Integer*>(args[0].get())->n;
            return IntegerV(-n);
        } else if (args[0]->v_type == V_RATIONAL) {
            int num = dynamic_cast<Rational*>(args[0].get())->numerator;
            int den = dynamic_cast<Rational*>(args[0].get())->denominator;
            return makeResult(-num, den);
        } else {
            throw RuntimeError("Wrong typename in -");
        }
    }
    // Handle multiple args: (- a b c) -> a - b - c
    int num, den;
    if (args[0]->v_type == V_INT) {
        num = dynamic_cast<Integer*>(args[0].get())->n;
        den = 1;
    } else if (args[0]->v_type == V_RATIONAL) {
        num = dynamic_cast<Rational*>(args[0].get())->numerator;
        den = dynamic_cast<Rational*>(args[0].get())->denominator;
    } else {
        throw RuntimeError("Wrong typename in -");
    }
    for (size_t i = 1; i < args.size(); i++) {
        int n, d;
        if (args[i]->v_type == V_INT) {
            n = dynamic_cast<Integer*>(args[i].get())->n;
            d = 1;
        } else if (args[i]->v_type == V_RATIONAL) {
            n = dynamic_cast<Rational*>(args[i].get())->numerator;
            d = dynamic_cast<Rational*>(args[i].get())->denominator;
        } else {
            throw RuntimeError("Wrong typename in -");
        }
        num = num * d - n * den;
        den = den * d;
    }
    return makeResult(num, den);
}

Value MultVar::evalRator(const std::vector<Value> &args) { // * with multiple args
    if (args.empty()) {
        return IntegerV(1);
    }
    int num = 1, den = 1;
    for (auto &arg : args) {
        if (arg->v_type == V_INT) {
            int n = dynamic_cast<Integer*>(arg.get())->n;
            num = num * n;
            den = den * 1;
        } else if (arg->v_type == V_RATIONAL) {
            int n = dynamic_cast<Rational*>(arg.get())->numerator;
            int d = dynamic_cast<Rational*>(arg.get())->denominator;
            num = num * n;
            den = den * d;
        } else {
            throw RuntimeError("Wrong typename in *");
        }
    }
    return makeResult(num, den);
}

Value DivVar::evalRator(const std::vector<Value> &args) { // / with multiple args
    if (args.empty()) {
        throw RuntimeError("Wrong number of arguments for /");
    }
    if (args.size() == 1) {
        // (/ x) -> 1/x
        if (args[0]->v_type == V_INT) {
            int n = dynamic_cast<Integer*>(args[0].get())->n;
            if (n == 0) {
                throw RuntimeError("Division by zero");
            }
            return makeResult(1, n);
        } else if (args[0]->v_type == V_RATIONAL) {
            int num = dynamic_cast<Rational*>(args[0].get())->numerator;
            int den = dynamic_cast<Rational*>(args[0].get())->denominator;
            if (num == 0) {
                throw RuntimeError("Division by zero");
            }
            return makeResult(den, num);
        } else {
            throw RuntimeError("Wrong typename in /");
        }
    }
    // (/ a b c) -> a / b / c
    int num, den;
    if (args[0]->v_type == V_INT) {
        num = dynamic_cast<Integer*>(args[0].get())->n;
        den = 1;
    } else if (args[0]->v_type == V_RATIONAL) {
        num = dynamic_cast<Rational*>(args[0].get())->numerator;
        den = dynamic_cast<Rational*>(args[0].get())->denominator;
    } else {
        throw RuntimeError("Wrong typename in /");
    }
    for (size_t i = 1; i < args.size(); i++) {
        int n, d;
        if (args[i]->v_type == V_INT) {
            n = dynamic_cast<Integer*>(args[i].get())->n;
            d = 1;
            if (n == 0) {
                throw RuntimeError("Division by zero");
            }
        } else if (args[i]->v_type == V_RATIONAL) {
            n = dynamic_cast<Rational*>(args[i].get())->numerator;
            d = dynamic_cast<Rational*>(args[i].get())->denominator;
            if (n == 0) {
                throw RuntimeError("Division by zero");
            }
        } else {
            throw RuntimeError("Wrong typename in /");
        }
        num = num * d;
        den = den * n;
    }
    return makeResult(num, den);
}

Value Expt::evalRator(const Value &rand1, const Value &rand2) { // expt
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int base = dynamic_cast<Integer*>(rand1.get())->n;
        int exponent = dynamic_cast<Integer*>(rand2.get())->n;
        
        if (exponent < 0) {
            throw(RuntimeError("Negative exponent not supported for integers"));
        }
        if (base == 0 && exponent == 0) {
            throw(RuntimeError("0^0 is undefined"));
        }
        
        long long result = 1;
        long long b = base;
        int exp = exponent;
        
        while (exp > 0) {
            if (exp % 2 == 1) {
                result *= b;
                if (result > INT_MAX || result < INT_MIN) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            b *= b;
            if (b > INT_MAX || b < INT_MIN) {
                if (exp > 1) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            exp /= 2;
        }
        
        return IntegerV((int)result);
    }
    throw(RuntimeError("Wrong typename"));
}

//A FUNCTION TO SIMPLIFY THE COMPARISON WITH INTEGER AND RATIONAL NUMBER
int compareNumericValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return (n1 < n2) ? -1 : (n1 > n2) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int left = r1->numerator;
        int right = n2 * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = n1 * r2->denominator;
        int right = r2->numerator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = r1->numerator * r2->denominator;
        int right = r2->numerator * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    throw RuntimeError("Wrong typename in numeric comparison");
}

Value Less::evalRator(const Value &rand1, const Value &rand2) { // <
    return BooleanV(compareNumericValues(rand1, rand2) < 0);
}

Value LessEq::evalRator(const Value &rand1, const Value &rand2) { // <=
    return BooleanV(compareNumericValues(rand1, rand2) <= 0);
}

Value Equal::evalRator(const Value &rand1, const Value &rand2) { // =
    return BooleanV(compareNumericValues(rand1, rand2) == 0);
}

Value GreaterEq::evalRator(const Value &rand1, const Value &rand2) { // >=
    return BooleanV(compareNumericValues(rand1, rand2) >= 0);
}

Value Greater::evalRator(const Value &rand1, const Value &rand2) { // >
    return BooleanV(compareNumericValues(rand1, rand2) > 0);
}

Value GreaterVar::evalRator(const std::vector<Value> &args) { // > with multiple args
    if (args.size() <= 1) {
        return BooleanV(true);
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) <= 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value LessVar::evalRator(const std::vector<Value> &args) { // < with multiple args
    // For multiple args: a < b < c < d -> check all adjacent pairs
    if (args.size() <= 1) {
        return BooleanV(true);
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) >= 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value LessEqVar::evalRator(const std::vector<Value> &args) { // <= with multiple args
    if (args.size() <= 1) {
        return BooleanV(true);
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) > 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value EqualVar::evalRator(const std::vector<Value> &args) { // = with multiple args
    if (args.size() <= 1) {
        return BooleanV(true);
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) != 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value GreaterEqVar::evalRator(const std::vector<Value> &args) { // >= with multiple args
    if (args.size() <= 1) {
        return BooleanV(true);
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) < 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value Cons::evalRator(const Value &rand1, const Value &rand2) { // cons
    return PairV(rand1, rand2);
}

Value ListFunc::evalRator(const std::vector<Value> &args) { // list function
    if (args.empty()) {
        return NullV();
    }
    Value result = NullV();
    for (auto it = args.rbegin(); it != args.rend(); ++it) {
        result = PairV(*it, result);
    }
    return result;
}

Value IsList::evalRator(const Value &rand) { // list?
    // An empty list is a list
    if (rand->v_type == V_NULL) {
        return BooleanV(true);
    }
    // Must be a chain of pairs ending with null
    Value current = rand;
    while (current->v_type == V_PAIR) {
        Pair *pair = dynamic_cast<Pair*>(current.get());
        current = pair->cdr;
    }
    return BooleanV(current->v_type == V_NULL);
}

Value Car::evalRator(const Value &rand) { // car
    if (rand->v_type != V_PAIR) {
        throw RuntimeError("car: expected pair");
    }
    return dynamic_cast<Pair*>(rand.get())->car;
}

Value Cdr::evalRator(const Value &rand) { // cdr
    if (rand->v_type != V_PAIR) {
        throw RuntimeError("cdr: expected pair");
    }
    return dynamic_cast<Pair*>(rand.get())->cdr;
}

Value SetCar::evalRator(const Value &rand1, const Value &rand2) { // set-car!
    if (rand1->v_type != V_PAIR) {
        throw RuntimeError("set-car!: expected pair as first argument");
    }
    dynamic_cast<Pair*>(rand1.get())->car = rand2;
    return VoidV();
}

Value SetCdr::evalRator(const Value &rand1, const Value &rand2) { // set-cdr!
    if (rand1->v_type != V_PAIR) {
        throw RuntimeError("set-cdr!: expected pair as first argument");
    }
    dynamic_cast<Pair*>(rand1.get())->cdr = rand2;
    return VoidV();
}

Value IsEq::evalRator(const Value &rand1, const Value &rand2) { // eq?
    // Check if type is Integer
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return BooleanV((dynamic_cast<Integer*>(rand1.get())->n) == (dynamic_cast<Integer*>(rand2.get())->n));
    }
    // Check if type is Boolean
    else if (rand1->v_type == V_BOOL && rand2->v_type == V_BOOL) {
        return BooleanV((dynamic_cast<Boolean*>(rand1.get())->b) == (dynamic_cast<Boolean*>(rand2.get())->b));
    }
    // Check if type is Symbol
    else if (rand1->v_type == V_SYM && rand2->v_type == V_SYM) {
        return BooleanV((dynamic_cast<Symbol*>(rand1.get())->s) == (dynamic_cast<Symbol*>(rand2.get())->s));
    }
    // Check if type is Null or Void
    else if ((rand1->v_type == V_NULL && rand2->v_type == V_NULL) ||
             (rand1->v_type == V_VOID && rand2->v_type == V_VOID)) {
        return BooleanV(true);
    } else {
        return BooleanV(rand1.get() == rand2.get());
    }
}

Value IsBoolean::evalRator(const Value &rand) { // boolean?
    return BooleanV(rand->v_type == V_BOOL);
}

Value IsFixnum::evalRator(const Value &rand) { // number?
    return BooleanV(rand->v_type == V_INT);
}

Value IsNull::evalRator(const Value &rand) { // null?
    return BooleanV(rand->v_type == V_NULL);
}

Value IsPair::evalRator(const Value &rand) { // pair?
    return BooleanV(rand->v_type == V_PAIR);
}

Value IsProcedure::evalRator(const Value &rand) { // procedure?
    return BooleanV(rand->v_type == V_PROC);
}

Value IsSymbol::evalRator(const Value &rand) { // symbol?
    return BooleanV(rand->v_type == V_SYM);
}

Value IsString::evalRator(const Value &rand) { // string?
    return BooleanV(rand->v_type == V_STRING);
}

Value Begin::eval(Assoc &e) {
    if (es.empty()) {
        return VoidV();
    }
    Value result = VoidV();
    for (auto &expr : es) {
        result = expr->eval(e);
    }
    return result;
}

// Forward declaration for quote evaluation
Value quoteEval(Syntax &s, Assoc &e);

Value quoteEval(Syntax &s, Assoc &e) {
    Number *num = dynamic_cast<Number*>(s.get());
    if (num != nullptr) {
        return IntegerV(num->n);
    }
    RationalSyntax *rat = dynamic_cast<RationalSyntax*>(s.get());
    if (rat != nullptr) {
        return RationalV(rat->numerator, rat->denominator);
    }
    TrueSyntax *t = dynamic_cast<TrueSyntax*>(s.get());
    if (t != nullptr) {
        return BooleanV(true);
    }
    FalseSyntax *f = dynamic_cast<FalseSyntax*>(s.get());
    if (f != nullptr) {
        return BooleanV(false);
    }
    SymbolSyntax *sym = dynamic_cast<SymbolSyntax*>(s.get());
    if (sym != nullptr) {
        return SymbolV(sym->s);
    }
    StringSyntax *str = dynamic_cast<StringSyntax*>(s.get());
    if (str != nullptr) {
        return StringV(str->s);
    }
    List *lst = dynamic_cast<List*>(s.get());
    if (lst != nullptr) {
        if (lst->stxs.empty()) {
            return NullV();
        }
        Value car_val = quoteEval(lst->stxs[0], e);
        Value cdr_val = NullV();
        for (auto it = lst->stxs.rbegin(); it != lst->stxs.rend(); ++it) {
            if (it == lst->stxs.rbegin()) {
                // last element is handled specially for dotted pairs?
                // Actually we just build it normally for quote
                continue;
            }
            Value val = quoteEval(*(it + 1), e);
            cdr_val = PairV(val, cdr_val);
        }
        // The full list is built correctly by chaining
        // Let's build from scratch properly
        if (lst->stxs.empty()) {
            return NullV();
        }
        Value current_cdr = NullV();
        for (auto it = lst->stxs.rbegin(); it != lst->stxs.rend(); ++it) {
            Value val = quoteEval(*it, e);
            current_cdr = PairV(val, current_cdr);
        }
        return current_cdr;
    }
    throw RuntimeError("Unknown syntax type in quote");
}

Value Quote::eval(Assoc& e) {
    return quoteEval(s, e);
}

Value AndVar::eval(Assoc &e) { // and with short-circuit evaluation
    if (rands.empty()) {
        return BooleanV(true);
    }
    Value last = VoidV();
    for (auto &expr : rands) {
        last = expr->eval(e);
        if (last->v_type == V_BOOL && !dynamic_cast<Boolean*>(last.get())->b) {
            return BooleanV(false);
        }
    }
    return last;
}

Value OrVar::eval(Assoc &e) { // or with short-circuit evaluation
    if (rands.empty()) {
        return BooleanV(false);
    }
    Value last = VoidV();
    for (auto &expr : rands) {
        last = expr->eval(e);
        if (!(last->v_type == V_BOOL && !dynamic_cast<Boolean*>(last.get())->b)) {
            return last;
        }
    }
    return last;
}

Value Not::evalRator(const Value &rand) { // not
    // In Scheme, any value not #f is considered true
    if (rand->v_type == V_BOOL && !dynamic_cast<Boolean*>(rand.get())->b) {
        return BooleanV(true);
    }
    return BooleanV(false);
}

Value If::eval(Assoc &e) {
    Value cond_val = cond->eval(e);
    if (cond_val->v_type == V_BOOL && !dynamic_cast<Boolean*>(cond_val.get())->b) {
        return alter->eval(e);
    } else {
        return conseq->eval(e);
    }
}

Value Cond::eval(Assoc &env) {
    for (auto &clause : clauses) {
        if (clause.empty()) {
            continue;
        }
        // Check if this is the else clause
        if (clause.size() == 1) {
            // Only condition, return its value
            return clause[0]->eval(env);
        }
        Value pred = clause[0]->eval(env);
        if (!(pred->v_type == V_BOOL && !dynamic_cast<Boolean*>(pred.get())->b)) {
            // Condition is true, evaluate all expressions in order, return last
            Value result = VoidV();
            for (size_t i = 1; i < clause.size(); i++) {
                result = clause[i]->eval(env);
            }
            return result;
        }
    }
    // No matched clause, return Void
    return VoidV();
}

Value Lambda::eval(Assoc &env) {
    return ProcedureV(x, e, env);
}

Value Apply::eval(Assoc &e) {
    if (rator->eval(e)->v_type != V_PROC) {throw RuntimeError("Attempt to apply a non-procedure");}

    Value proc_val = rator->eval(e);
    Procedure* clos_ptr = dynamic_cast<Procedure*>(proc_val.get());

    // Evaluate all arguments
    std::vector<Value> args;
    for (auto &arg : rand) {
        args.push_back(arg->eval(e));
    }
    if (args.size() != clos_ptr->parameters.size()) {
        throw RuntimeError("Wrong number of arguments");
    }

    // Extend the closure environment with the arguments
    Assoc param_env = clos_ptr->env;
    for (size_t i = 0; i < clos_ptr->parameters.size(); i++) {
        param_env = extend(clos_ptr->parameters[i], args[i], param_env);
    }

    return clos_ptr->e->eval(param_env);
}

Value Define::eval(Assoc &env) {
    // Check if name conflicts with primitives or reserved words
    if (primitives.count(var) > 0 || reserved_words.count(var) > 0) {
        throw RuntimeError("Cannot redefine primitive/reserved word: " + var);
    }
    Value val = e->eval(env);
    env.ptr.reset(new AssocList(var, val, env));
    return VoidV();
}

Value Let::eval(Assoc &env) {
    // let is syntactic sugar for: ((lambda (params) body) values...)
    // Evaluate all values first in outer environment
    Assoc new_env = env;
    for (auto &binding : bind) {
        Value val = binding.second->eval(env);
        new_env = extend(binding.first, val, new_env);
    }
    return body->eval(new_env);
}

Value Letrec::eval(Assoc &env) {
    // Step 1: create new scope based on current, bind all vars to nullptr
    Assoc env1 = env;
    for (auto &binding : bind) {
        env1 = extend(binding.first, Value(nullptr), env1);
    }
    // Step 2: evaluate expressions in env1, get values
    // Step 3: modify the bindings to their values
    for (auto &binding : bind) {
        Value val = binding.second->eval(env1);
        modify(binding.first, val, env1);
    }
    // Step 4: evaluate body in the extended environment
    return body->eval(env1);
}

Value Set::eval(Assoc &env) {
    Value val = e->eval(env);
    modify(var, val, env);
    return VoidV();
}

Value Display::evalRator(const Value &rand) { // display function
    if (rand->v_type == V_STRING) {
        String* str_ptr = dynamic_cast<String*>(rand.get());
        std::cout << str_ptr->s;
    } else {
        rand->show(std::cout);
    }
    
    return VoidV();
}
