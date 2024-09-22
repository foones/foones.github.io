
// Prover

class Derivation {

  constructor(parent, prover, conclusion) {
    let self = this;
    this._parent = parent;
    this._prover = prover;
    this._conclusion = conclusion;

    let conclusion_elem = DIV('sequent', [TEXT(this._conclusion.toString())]);
    conclusion_elem.onclick = function () {
      self._prover.toggle_select(self);
    };
    this._conclusion_elem = conclusion_elem;
    this._premises_elem = DIV('premises', []);
    this._elem = DIV('derivation', [
      this._premises_elem,
      this._conclusion_elem
    ]);
    this._rule_name = null;
    this._subderivations = [];
  }

  parent() {
    return this._parent;
  }

  conclusion() {
    return this._conclusion;
  }

  element() {
    return this._elem;
  }

  is_selected() {
    return this._conclusion_elem.classList.contains('selected');
  }

  select() {
    this._conclusion_elem.classList.add('selected');
  }

  unselect() {
    this._conclusion_elem.classList.remove('selected');
  }

  apply_rule(rule, args) {
    this._prover.extend_derivation_tree(
      this,
      rule.name(),
      rule.premises(this.conclusion(), args)
    );
  }

  prune_derivation_tree() {
    this._rule_name = null;
    clearElem(this._premises_elem);
    this._premises_elem.classList.remove('proved');
    this._subderivations = [];
  }

  subderivations() {
    return this._subderivations;
  }

  _create_rule_name(rule_name) {
    return DIV('rule_name', [TEXT(rule_name)]);
  }

  extend_derivation_tree(rule_name, subderivations) {
    this._prover.prune_derivation_tree(this);
    this._rule_name = rule_name;
    this._subderivations = subderivations;
    for (let subderivation of subderivations) {
      this._premises_elem.appendChild(subderivation.element());
    }
    this._premises_elem.classList.add('proved');
    this._premises_elem.appendChild(this._create_rule_name(rule_name));

    let next_goal = this.search_next_goal();
    if (next_goal !== null) {
      this._prover.toggle_select(next_goal);
    }
  }

  has_been_proved() {
    return this._rule_name !== null;
  }

  search_unproved_descendant() {
    if (!this.has_been_proved()) {
      return this;
    }
    let subderivations = this.subderivations();
    for (let subderivation of subderivations) {
      let res = subderivation.search_unproved_descendant();
      if (res !== null) {
        return res;
      }
    }
    return null;
  }

  search_next_goal() {
    let current = this;
    while (current !== null) {
      let res = current.search_unproved_descendant();
      if (res !== null) {
        return res;
      }
      current = current.parent();
    }
    return null;
  }

}

class Prover {

  constructor(derivation_elem, options_elem) {
    this._all_rules = [
      new RuleAxiom(),
      new RuleAndI(),
      new RuleImpI(),
      new RuleOrI1(),
      new RuleOrI2(),
      new RuleTopI(),
      new RuleNegI(),
      new RuleForallI(),
      new RuleExistsI(),
      //
      new RuleAndE1(),
      new RuleAndE2(),
      new RuleImpE(),
      new RuleOrE(),
      new RuleBotE(),
      new RuleNegE(),
      new RuleForallE(),
      new RuleExistsE(),
      new RuleLEM(),
    ];
    this._derivation_elem = derivation_elem;
    this._options_elem = options_elem;
    this._derivations = [];
  }

  start_proving(sequent) {
    let derivation = this._create_derivation(null, sequent);
    this._derivation_elem.appendChild(derivation.element());
    this.toggle_select(derivation);
  }

  toggle_select(derivation) {
    this._unselect_all();
    derivation.select();
    this._show_options_for(derivation);
  }

  _create_derivation(parent, sequent) {
    let derivation = new Derivation(parent, this, sequent);
    this._derivations.push(derivation);
    return derivation;
  }

  _remove_derivation(derivation) {
    this._derivations = this._derivations.filter(function (d) {
      return d != derivation;
    });
  }

  _unselect_all() {
    for (let other of this._derivations) {
      other.unselect();
    }
  }

  _close_options() {
    clearElem(this._options_elem);
  }

  _show_options_for(derivation) {
    this._close_options();
    let anyOption = false;
    let options_elem = DIV('options', []);

    if (derivation.has_been_proved()) {
      options_elem.appendChild(this._option_clear(derivation));
    }

    for (let rule of this._all_rules) {
      if (rule.can_be_applied(derivation.conclusion())) {
        options_elem.appendChild(this._option_apply_rule(derivation, rule));
        anyOption = true;
      }
    }
    if (!anyOption) {
      elem.appendChild(TEXT('No rule applies'));
    }
    this._options_elem.appendChild(options_elem);
  }

  _option_clear(derivation) {
    let self = this;
    let button = BUTTON('(limpiar)', function () {
      self.prune_derivation_tree(derivation);
      self._show_options_for(derivation);
    });
    button.classList.add('clear_button');
    return DIV('option', [button]);
  }

  _option_apply_rule(derivation, rule) {
    let self = this;
    let parameter_elems = [];
    for (let parameter of rule.parameters()) {
      parameter_elems.push(INPUT_TEXT(parameter.default_value()));
    }
    let errmsg = DIV('errmsg', []);
    let button = BUTTON(rule.name(), function () {
      let args = [];
      for (let elem of parameter_elems) {
        args.push(elem.value);
      }
      let check = rule.can_be_applied_with_args(derivation.conclusion(), args);
      if (check[0]) {
        self._unselect_all();
        self._close_options();
        derivation.apply_rule(rule, args);
      } else {
        clearElem(errmsg);
        errmsg.appendChild(P(TEXT(check[1])));
      }
    });
    let option = DIV('option', [button].concat(parameter_elems).concat([errmsg]));
    return option;
  }

  extend_derivation_tree(derivation, rule_name, premises) {
    let subderivations = [];
    for (let premise of premises) {
      subderivations.push(this._create_derivation(derivation, premise));
    }
    derivation.extend_derivation_tree(rule_name, subderivations);
  }

  prune_derivation_tree(derivation) {
    for (let subderivation of derivation.subderivations()) {
      this.prune_derivation_tree(subderivation);
      this._remove_derivation(subderivation);
    }
    derivation.prune_derivation_tree();
  }

}

//

let sequent1 = 
    new Sequent(
      new Context([
        new FAnd(new FPred('q', []), new FPred('p', [])),
      ]),
      new FAnd(new FPred('p', []), new FPred('q', []))
    );

let sequent2 = 
    new Sequent(
      new Context([
      ]),
      new FImp(new FPred('p', []),
        new FImp(new FPred('q', []), new FPred('p', [])))
    );
let sequent3 = 
    new Sequent(
      new Context([
      ]),
      new FImp(
        new FImp(new FPred('p', []), new FImp(new FPred('q', []), new FPred('r', []))),
        new FImp(
          new FImp(new FPred('p', []), new FPred('q', [])),
          new FImp(new FPred('p', []), new FPred('r', [])),
        ))
    );
let sequent4 = 
    new Sequent(
      new Context([
        new FOr(new FPred('q', []), new FPred('p', []))
      ]),
      new FOr(new FPred('p', []), new FPred('q', []))
    );
let sequent5 = 
    new Sequent(
      new Context([
        new FOr(new FPred('q', []), new FPred('p', []))
      ]),
      new FTrue()
    );
let sequent6 = 
    new Sequent(
      new Context([
      ]),
      new FNeg(
        new FAnd(
          new FPred('p', []),
          new FNeg(new FPred('p', [])),
        )
      )
    );
let sequent7 = 
    new Sequent(
      new Context([
        new FPred('p', [new Term('x', [])])
      ]),
      new FForall('x',
        new FOr(
          new FPred('p', [new Term('x', [])]),
          new FNeg(new FPred('p', [new Term('x', [])]))
        )
      )
    );

function main() {
  let derivation_elem = document.getElementById('derivation');
  let options_elem = document.getElementById('options');
  let prompt_elem = document.getElementById('prompt');
  let input_formula = INPUT_TEXT("forall x p(x), forall x q(x) |- forall x (p(x) & q(x))");
  let start_button = BUTTON('Empezar', function () {
    clearElem(derivation_elem);
    clearElem(options_elem);
    let prover = new Prover(derivation_elem, options_elem);
    let parser = new Parser();
    let msequent = parser.parse_sequent(input_formula.value);
    if (msequent[0]) {
      prover.start_proving(msequent[1]);
    } else {
      console.log(msequent[1]);
    }
  });
  prompt_elem.appendChild(input_formula);
  prompt_elem.appendChild(start_button);
  input_formula.select();
  input_formula.focus();
  start_button.onclick();
}

