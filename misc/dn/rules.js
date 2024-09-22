
// Parameter types

class ParameterTerm {
  constructor(default_value) {
    this._default_value = default_value;
  }

  default_value() {
    return this._default_value;
  }

  well_formed_value(value) {
    // Check that the value is a well-formed term
    let parser = new Parser();
    // returns [bool, x], where x is an error message if the bool is false
    return parser.parse_term(value);
  }

  unwrap_value(value) {
    // Unwrap value to a term
    let parser = new Parser();
    let mform = parser.parse_term(value);
    return mform[1];
  }
}

class ParameterFormula {
  constructor(default_value) {
    this._default_value = default_value;
  }

  default_value() {
    return this._default_value;
  }

  well_formed_value(value) {
    // Check that the value is a well-formed formula
    let parser = new Parser();
    // returns [bool, x], where x is an error message if the bool is false
    return parser.parse_formula(value);
  }

  unwrap_value(value) {
    // Unwrap value to a formula
    let parser = new Parser();
    let mform = parser.parse_formula(value);
    return mform[1];
  }
}

// Rules

class Rule {

  can_be_applied_with_args(sequent, text_args) {
    if (!this.can_be_applied(sequent)) {
      return [false, 'La regla no se puede aplicar'];
    }
    let params = this.parameters();
    if (text_args.length !== params.length) {
      return [false, 'Cantidad de parámetros insuficiente'];
    }
    for (let i = 0; i < params.length; i++) {
      let wf = params[i].well_formed_value(text_args[i]);
      if (!wf[0]) {
        return wf;
      }
    }
    if (this.check_valid_arguments(sequent, this.unwrap_args(text_args))) {
      return [true, null];
    } else {
      return [false, 'Parámetros inválidos'];
    }
  }

  check_valid_arguments(sequent, args) {
    return true;
  }

  unwrap_args(args) {
    let uargs = [];
    let params = this.parameters();
    for (let i = 0; i < params.length; i++) {
      uargs.push(params[i].unwrap_value(args[i]));
    }
    return uargs;
  }
}

class RuleAxiom extends Rule {

  constructor() {
    super();
  }

  name() {
    return 'ax';
  }

  parameters() {
    return [];
  }

  can_be_applied(sequent) {
    return sequent.context().contains_formula(sequent.thesis());
  }

  premises(sequent, text_args) {
    return [];
  }
}

class RuleAndI extends Rule {

  constructor() {
    super();
  }

  name() {
    return CHR_AND + 'i';
  }

  parameters() {
    return [];
  }

  can_be_applied(sequent) {
    return sequent.thesis().shape() === CHR_AND;
  }

  premises(sequent, text_args) {
    return [
      new Sequent(sequent.context(), sequent.thesis().subformulas()[0]),
      new Sequent(sequent.context(), sequent.thesis().subformulas()[1])
    ];
  }
}

class RuleAndE1 extends Rule {

  constructor() {
    super();
  }

  name() {
    return CHR_AND + 'e1';
  }

  parameters() {
    return [new ParameterFormula('p')];
  }

  can_be_applied(sequent) {
    return true;
  }

  premises(sequent, text_args) {
    let args = this.unwrap_args(text_args);
    return [
      new Sequent(sequent.context(), new FAnd(sequent.thesis(), args[0]))
    ];
  }
}

class RuleAndE2 extends Rule {

  constructor() {
    super();
  }

  name() {
    return CHR_AND + 'e2';
  }

  parameters() {
    return [new ParameterFormula('p')];
  }

  can_be_applied(sequent) {
    return true;
  }

  premises(sequent, text_args) {
    let args = this.unwrap_args(text_args);
    return [
      new Sequent(sequent.context(), new FAnd(args[0], sequent.thesis()))
    ];
  }
}

class RuleImpI extends Rule {

  constructor() {
    super();
  }

  name() {
    return CHR_IMP + 'i';
  }

  parameters() {
    return [];
  }

  can_be_applied(sequent) {
    return sequent.thesis().shape() === CHR_IMP;
  }

  premises(sequent, text_args) {
    return [
      new Sequent(sequent.context().extend(sequent.thesis().subformulas()[0]),
                  sequent.thesis().subformulas()[1])
    ];
  }
}
class RuleImpE extends Rule {

  constructor() {
    super();
  }

  name() {
    return CHR_IMP + 'e';
  }

  parameters() {
    return [new ParameterFormula('p')];
  }

  can_be_applied(sequent) {
    return true;
  }

  premises(sequent, text_args) {
    let args = this.unwrap_args(text_args);
    return [
      new Sequent(sequent.context(), new FImp(args[0], sequent.thesis())),
      new Sequent(sequent.context(), args[0])
    ];
  }
}

class RuleOrI1 extends Rule {

  constructor() {
    super();
  }

  name() {
    return CHR_OR + 'i1';
  }

  parameters() {
    return [];
  }

  can_be_applied(sequent) {
    return sequent.thesis().shape() === CHR_OR;
  }

  premises(sequent, text_args) {
    return [
      new Sequent(sequent.context(), sequent.thesis().subformulas()[0])
    ];
  }
}

class RuleOrI2 extends Rule {

  constructor() {
    super();
  }

  name() {
    return CHR_OR + 'i2';
  }

  parameters() {
    return [];
  }

  can_be_applied(sequent) {
    return sequent.thesis().shape() === CHR_OR;
  }

  premises(sequent, text_args) {
    return [
      new Sequent(sequent.context(), sequent.thesis().subformulas()[1])
    ];
  }
}

class RuleOrE extends Rule {

  constructor() {
    super();
  }

  name() {
    return CHR_OR + 'e';
  }

  parameters() {
    return [new ParameterFormula('p' + CHR_OR + 'q')];
  }

  can_be_applied(sequent) {
    return true;
  }
  
  check_valid_arguments(sequent, args) {
    return args[0].shape() === CHR_OR;
  }

  premises(sequent, text_args) {
    let args = this.unwrap_args(text_args);
    let target = args[0];
    return [
      new Sequent(sequent.context(), args[0]),
      new Sequent(sequent.context().extend(args[0].subformulas()[0]), sequent.thesis()),
      new Sequent(sequent.context().extend(args[0].subformulas()[1]), sequent.thesis())
    ];
  }
}

class RuleTopI extends Rule {

  constructor() {
    super();
  }

  name() {
    return CHR_TOP + 'i';
  }

  parameters() {
    return [];
  }

  can_be_applied(sequent) {
    return sequent.thesis().shape() === CHR_TOP;
  }

  premises(sequent, text_args) {
    return [];
  }
}

class RuleBotE extends Rule {

  constructor() {
    super();
  }

  name() {
    return CHR_BOT + 'e';
  }

  parameters() {
    return [];
  }

  can_be_applied(sequent) {
    return true;
  }

  premises(sequent, text_args) {
    return [new Sequent(sequent.context(), new FFalse())];
  }
}

class RuleNegI extends Rule {

  constructor() {
    super();
  }

  name() {
    return CHR_NEG + 'i';
  }

  parameters() {
    return [];
  }

  can_be_applied(sequent) {
    return sequent.thesis().shape() === CHR_NEG;
  }

  premises(sequent, text_args) {
    return [
      new Sequent(sequent.context().extend(sequent.thesis().subformulas()[0]),
                  new FFalse())
    ];
  }
}

class RuleNegE extends Rule {

  constructor() {
    super();
  }

  name() {
    return CHR_NEG + 'e';
  }

  parameters() {
    return [new ParameterFormula('p')];
  }

  can_be_applied(sequent) {
    return sequent.thesis().shape() === CHR_BOT;
  }

  premises(sequent, text_args) {
    let args = this.unwrap_args(text_args);
    return [
      new Sequent(sequent.context(), new FNeg(args[0])),
      new Sequent(sequent.context(), args[0])
    ];
  }
}

class RuleForallI extends Rule {

  constructor() {
    super();
  }

  name() {
    return CHR_FORALL + 'i';
  }

  parameters() {
    return [];
  }

  can_be_applied(sequent) {
    return sequent.thesis().shape() === CHR_FORALL;
  }

  premises(sequent, text_args) {
    let args = this.unwrap_args(text_args);
    let body_old = sequent.thesis().body();
    let forbidden = sequent.free_variables();
    let x_old = sequent.thesis().variable();
    let x_new = variable_apart_from(x_old, forbidden);
    let body_new = body_old.substitute(x_old, new Term(x_new, []));
    return [
      new Sequent(sequent.context(), body_new),
    ];
  }

}

class RuleForallE extends Rule {

  constructor() {
    super();
  }

  name() {
    return CHR_FORALL + 'e';
  }

  parameters() {
    return [new ParameterFormula(CHR_FORALL + 'x p(x)'), new ParameterTerm('t')];
  }

  can_be_applied(sequent) {
    return true;
  }

  check_valid_arguments(sequent, args) {
    let formula = args[0];
    let x = formula.variable();
    let body = formula.body();
    let term = args[1];
    if (args[0].shape() !== CHR_FORALL) {
      return false;
    }
    return body.substitute(x, term).equals(sequent.thesis());
  }

  premises(sequent, text_args) {
    let args = this.unwrap_args(text_args);
    return [
      new Sequent(sequent.context(), args[0]),
    ];
  }
}

class RuleExistsI extends Rule {

  constructor() {
    super();
  }

  name() {
    return CHR_EXISTS + 'i';
  }

  parameters() {
    return [new ParameterTerm('t')];
  }

  can_be_applied(sequent) {
    return sequent.thesis().shape() === CHR_EXISTS;
  }

  premises(sequent, text_args) {
    let args = this.unwrap_args(text_args);
    let witness = args[0];
    let formula = sequent.thesis();
    let x = formula.variable();
    let body = formula.body();
    let instantiated_body = body.substitute(x, witness);
    return [
      new Sequent(sequent.context(), instantiated_body),
    ];
  }
}

class RuleExistsE extends Rule {

  constructor() {
    super();
  }

  name() {
    return CHR_EXISTS + 'e';
  }

  parameters() {
    return [new ParameterFormula(CHR_EXISTS + ' x p(x)')];
  }

  can_be_applied(sequent) {
    return true;
  }

  premises(sequent, text_args) {
    let args = this.unwrap_args(text_args);
    let existential_formula = args[0];
    let body_old = existential_formula.body();
    let forbidden = sequent.free_variables();
    let x_old = existential_formula.variable();
    let x_new = variable_apart_from(x_old, forbidden);
    let body_new = body_old.substitute(x_old, new Term(x_new, []));
    return [
      new Sequent(sequent.context(), existential_formula),
      new Sequent(sequent.context().extend(body_new), sequent.thesis())
    ];
  }
}

class RuleLEM extends Rule {

  constructor() {
    super();
  }

  name() {
    return 'LEM';
  }

  parameters() {
    return [];
  }

  can_be_applied(sequent) {
    let a = new FNeg(sequent.thesis().subformulas()[0]);
    let b = sequent.thesis().subformulas()[1];
    return sequent.thesis().shape() === CHR_OR && a.equals(b);
  }

  premises(sequent, text_args) {
    return [];
  }
}

