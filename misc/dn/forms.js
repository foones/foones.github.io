
const FORM_PRED = 'PRED';

function set_union(s1, s2) {
  let res = new Set();
  for (let x of s1) {
    res.add(x);
  }
  for (let x of s2) {
    res.add(x);
  }
  return res;
}

function set_difference(s1, s2) {
  let res = new Set();
  for (let x of s1) {
    if (!s2.has(x)) {
      res.add(x);
    }
  }
  return res;
}

function variable_apart_from(prefix, forbidden) {
  if (!forbidden.has(prefix)) {
    return prefix;
  }
  let suffix = 0;
  while (forbidden.has(prefix + suffix.toString())) {
    suffix++;
  }
  return prefix + suffix.toString();
}

// Terms

function equal_lists(xs1, xs2) {
  if (xs1.length !== xs2.length) {
    return false;
  }
  for (let i = 0; i < xs1.length; i++) {
    if (!xs1[i].equals(xs2[i])) {
      return false;
    }
  }
  return true;
}

function show_list(xs) {
  let res = [];
  for (let x of xs) {
    res.push(x.toString());
  }
  return res;
}

class Term {
  constructor(function_symbol, subterms) {
    this._function_symbol = function_symbol;
    this._subterms = subterms;
  }

  function_symbol() {
    return this._function_symbol;
  }

  subterms() {
    return this._subterms;
  }

  equals(other) {
    return this.function_symbol() === other.function_symbol()
        && equal_lists(this.subterms(), other.subterms());
  }

  toString() {
    let args = show_list(this._subterms);
    if (args.length === 0) {
      return this._function_symbol;
    } else {
      return this._function_symbol + '(' + args.join(', ') + ')';
    }
  }
  
  free_variables() {
    if (this._subterms.length === 0) {
      return new Set([this._function_symbol]);
    } else {
      let res = new Set();
      for (let subterm of this._subterms) {
        res = set_union(res, subterm.free_variables());
      }
      return res;
    }
  }

  substitute(x, term) {
    if (this._subterms.length === 0 && this._function_symbol === x) {
      return term;
    } else {
      return new Term(this.function_symbol(),
                      this.subterms().map(t => t.substitute(x, term)));
    }
  }
}

// Formulae

class Formula {
  equals(other) {
    return this.shape() === other.shape()
        && equal_lists(this.subformulas(), other.subformulas());
  }

  free_variables() {
    let res = new Set();
    for (let subformula of this.subformulas()) {
      res = set_union(res, subformula.free_variables());
    }
    return res;
  }
}

class FPred extends Formula {
  constructor(predicate_symbol, terms) {
    super();
    this._predicate_symbol = predicate_symbol;
    this._terms = terms;
  }
  
  shape() {
    return FORM_PRED;
  }

  subformulas() {
    return [];
  }

  predicate_symbol() {
    return this._predicate_symbol;
  }

  terms() {
    return this._terms;
  }
 
  toString() {
    let args = show_list(this._terms);
    if (args.length === 0) {
      return this._predicate_symbol;
    } else {
      return this._predicate_symbol + '(' + args.join(', ') + ')';
    }
  }

  equals(other) {
    return this.shape() === other.shape()
        && this.predicate_symbol() === other.predicate_symbol()
        && equal_lists(this.terms(), other.terms());
  }

  free_variables() {
    let res = new Set();
    for (let term of this.terms()) {
      res = set_union(res, term.free_variables());
    }
    return res;
  }

  substitute(x, term) {
    return new FPred(this.predicate_symbol(),
                     this.terms().map(t => t.substitute(x, term)));
  }
}

class FNullaryFormula extends Formula {

  constructor(op) {
    super();
    this._op = op;
  }

  shape() {
    return this._op;
  }
  
  subformulas() {
    return [];
  }

  toString() {
    return this._op;
  }

  substitute(x, term) {
    return this;
  }
}

class FTrue extends FNullaryFormula {
  constructor(op) {
    super(CHR_TOP);
  }
}

class FFalse extends FNullaryFormula {
  constructor(op) {
    super(CHR_BOT);
  }
}

class FUnaryFormula extends Formula {

  constructor(op, form) {
    super();
    this._op = op;
    this._form = form;
  }

  shape() {
    return this._op;
  }
  
  subformulas() {
    return [this._form];
  }

  toString() {
    return this._op + this._form.toString();
  }
}

class FNeg extends FUnaryFormula {
  constructor(form) {
    super(CHR_NEG, form);
  }

  substitute(x, term) {
    return new FNeg(this.subformulas()[0].substitute(x, term));
  }
}

class FBinaryFormula extends Formula {

  constructor(op, form0, form1) {
    super();
    this._op = op;
    this._form0 = form0;
    this._form1 = form1;
  }

  shape() {
    return this._op;
  }
  
  subformulas() {
    return [this._form0, this._form1];
  }

  toString() {
    return '(' + this._form0.toString() + this._op + this._form1.toString() + ')';
  }
}

class FAnd extends FBinaryFormula {
  constructor(form0, form1) {
    super(CHR_AND, form0, form1);
  }

  substitute(x, term) {
    return new FAnd(this.subformulas()[0].substitute(x, term),
                    this.subformulas()[1].substitute(x, term));
  }
}

class FOr extends FBinaryFormula {
  constructor(form0, form1) {
    super(CHR_OR, form0, form1);
  }

  substitute(x, term) {
    return new FOr(this.subformulas()[0].substitute(x, term),
                   this.subformulas()[1].substitute(x, term));
  }
}

class FImp extends FBinaryFormula {
  constructor(form0, form1) {
    super(CHR_IMP, form0, form1);
  }

  substitute(x, term) {
    return new FImp(this.subformulas()[0].substitute(x, term),
                    this.subformulas()[1].substitute(x, term));
  }
}

class FQuantifiedFormula extends Formula {

  constructor(op, variable, form) {
    super();
    this._op = op;
    this._variable = variable;
    this._form = form;
  }

  shape() {
    return this._op;
  }

  equals(other) {
    if (this.shape() !== other.shape()) {
      return false;
    }
    let forbidden = set_union(this.free_variables(), other.free_variables());
    let x = this.variable();
    let y = other.variable();
    let z = variable_apart_from(x, forbidden);
    let body1 = this.body().substitute(x, new Term(z, []));
    let body2 = other.body().substitute(y, new Term(z, []));
    return body1.equals(body2);
  }
  
  variable() {
    return this._variable;
  }

  body() {
    return this._form;
  }
  
  subformulas() {
    return [this._form];
  }

  toString() {
    return this._op + this._variable + '.' + this._form.toString();
  }

  free_variables() {
    return set_difference(this._form.free_variables(), new Set([this._variable]));
  }
}

class FForall extends FQuantifiedFormula {
  constructor(variable, form) {
    super(CHR_FORALL, variable, form);
  }

  substitute(x, term) {
    let y_old = this.variable();
    let body_old = this.subformulas()[0];
    let forbidden =
        set_union(Set([x]),
          set_union(set_difference(body_old.free_variables(), new Set([y_old])),
                    term.free_variables()));
    let y_new = variable_apart_from(y_old, forbidden);
    let body_new = body_old.substitute(y_old, Term(y_new, []))
                           .substitute(x, term);
    return new FForall(y_new, body_new);
  }
}

class FExists extends FQuantifiedFormula {
  constructor(variable, form) {
    super(CHR_EXISTS, variable, form);
  }

  substitute(x, term) {
    let y_old = this.variable();
    let body_old = this.subformulas()[0];
    let forbidden =
        set_union(Set([x]),
          set_union(set_difference(body_old.free_variables(), new Set([y_old])),
                    term.free_variables()));
    let y_new = variable_apart_from(y_old, forbidden);
    let body_new = body_old.substitute(y_old, Term(y_new, []))
                           .substitute(x, term);
    return new FExists(y_new, body_new);
  }
}

class Context {
  constructor(assumptions) {
    this._assumptions = assumptions;
  }

  assumptions() {
    return Array.from(this._assumptions);
  }

  extend(form) {
    return new Context(this._assumptions.concat([form]));
  }

  toString() {
    let parts = [];
    for (let assumption of this._assumptions) {
      parts.push(assumption.toString());
    }
    return parts.join(',');
  }

  contains_formula(formula) {
    for (let assumption of this._assumptions) {
      if (formula.equals(assumption)) {
        return true;
      }
    }
    return false;
  }

  free_variables() {
    let res = new Set([]);
    for (let assumption of this._assumptions) {
      res = set_union(res, assumption.free_variables());
    }
    return res;
  }

}

class Sequent {

  constructor(context, thesis) {
    this._context = context;
    this._thesis = thesis;
  }

  context() {
    return this._context;
  }

  thesis() {
    return this._thesis;
  }

  toString() {
    return this._context + CHR_TURNSTILE + this._thesis;
  }

  free_variables() {
    return set_union(this._context.free_variables(), this._thesis.free_variables());
  }

}

