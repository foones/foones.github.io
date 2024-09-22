
class SyntaxError extends Error {
  constructor(message) {
    super(message);
    this._message = message;
  }

  message() {
    return this._message;
  }
}

function at(string, i, substr) {
  return string.slice(i, i + substr.length) === substr;
}

function is_ident(chr) {
  return chr === '_'
      || '0' <= chr && chr <= '9'
      || 'A' <= chr && chr <= 'Z'
      || 'a' <= chr && chr <= 'z';
}

function tokenize(string) {
  let tokens = [];
  let i = 0;
  while (i < string.length) {
    if (string[i] === ' ' || string[i] === '.') {
      i++;
    } else if (string[i] === '(') {
      tokens.push('(');
      i++;
    } else if (string[i] === ')') {
      tokens.push(')');
      i++;
    } else if (string[i] === ',') {
      tokens.push(',');
      i++;
    } else if (string[i] === CHR_TURNSTILE) {
      tokens.push(CHR_TURNSTILE);
      i++;
    } else if (at(string, i, '|-')) {
      tokens.push(CHR_TURNSTILE);
      i += 2; 
    } else if (string[i] === CHR_BOT) {
      tokens.push(CHR_BOT);
      i++;
    } else if (string[i] === CHR_TOP) {
      tokens.push(CHR_TOP);
      i++;
    } else if (string[i] === CHR_AND || string[i] === '^' || string[i] === '&' || string[i] === '*') {
      tokens.push(CHR_AND);
      i++;
    } else if (string[i] === CHR_OR || string[i] === '|' || string[i] === '+') {
      tokens.push(CHR_OR);
      i++;
    } else if (string[i] === CHR_IMP || string[i] === '→') {
      tokens.push(CHR_IMP);
      i++; 
    } else if (at(string, i, '->') || at(string, i, '=>')) {
      tokens.push(CHR_IMP);
      i += 2; 
    } else if (string[i] === CHR_NEG || string[i] === '~') {
      tokens.push(CHR_NEG);
      i++;
    } else if (string[i] === CHR_FORALL || string[i] === '!') {
      tokens.push(CHR_FORALL);
      i++;
    } else if (string[i] === CHR_EXISTS || string[i] === '?') {
      tokens.push(CHR_EXISTS);
      i++;
    } else if (is_ident(string[i])) {
      let id = '';
      while (i < string.length && is_ident(string[i])) {
        id += string[i];
        i++;
      }
      id = id.toLowerCase();
      if (id === 'false') {
        tokens.push(CHR_BOT);
      } else if (id === 'true') {
        tokens.push(CHR_TOP);
      } else if (id === 'and') {
        tokens.push(CHR_AND);
      } else if (id === 'or') {
        tokens.push(CHR_OR);
      } else if (id === 'imp') {
        tokens.push(CHR_IMP);
      } else if (id === 'not') {
        tokens.push(CHR_NOT);
      } else if (id === 'forall') {
        tokens.push(CHR_FORALL);
      } else if (id === 'exists') {
        tokens.push(CHR_EXISTS);
      } else {
        tokens.push([id]);
      }
    } else {
      throw new SyntaxError('Error léxico');
    }
  }
  return tokens;
}

class Parser {
  constructor() {
  }

  parse_formula(source) {
    try {
      this._tokens = tokenize(source);
      let form = this._parse_formula();
      if (this._tokens.length !== 0) {
        throw new SyntaxError('Entrada demasiado larga.');
      }
      return [true, form];
    } catch (err) {
      if (err instanceof SyntaxError) {
        return [false, err];
      } else {
        throw err;
      }
    }
  }

  parse_term(source) {
    try {
      this._tokens = tokenize(source);
      let term = this._parse_term();
      if (this._tokens.length !== 0) {
        throw new SyntaxError('Entrada demasiado larga.');
      }
      return [true, term];
    } catch (err) {
      if (err instanceof SyntaxError) {
        return [false, err];
      } else {
        throw err;
      }
    }
  }

  parse_sequent(source) {
    try {
      this._tokens = tokenize(source);
      let sequent = this._parse_sequent();
      if (this._tokens.length !== 0) {
        throw new SyntaxError('Entrada demasiado larga.');
      }
      return [true, sequent];
    } catch (err) {
      if (err instanceof SyntaxError) {
        return [false, err];
      } else {
        throw err;
      }
    }
  }

  _parse_sequent() {
    let context = this._parse_context();
    if (this._tokens.length > 0 && this._tokens[0] === CHR_TURNSTILE) {
      this._tokens.shift();
      let thesis = this._parse_formula();
      return new Sequent(context, thesis);
    } else if (context.assumptions().length === 1) {
      return new Sequent(new Context([]), context.assumptions()[0]);
    } else {
      throw new SyntaxError('El secuente no está bien formado.');
    }
  }

  _parse_context() {
    let assumptions = [];
    assumptions.push(this._parse_formula());
    while (this._tokens.length > 0 && this._tokens[0] === ',') {
      this._tokens.shift();
      assumptions.push(this._parse_formula());
    }
    return new Context(assumptions);
  }

  _parse_formula() {
    let form1 = this._parse_atomic_formula();
    if (this._tokens.length > 0 && this._tokens[0] === CHR_AND) {
      this._tokens.shift();
      let form2 = this._parse_formula();
      return new FAnd(form1, form2);
    } else if (this._tokens.length > 0 && this._tokens[0] === CHR_OR) {
      this._tokens.shift();
      let form2 = this._parse_formula();
      return new FOr(form1, form2);
    } else if (this._tokens.length > 0 && this._tokens[0] === CHR_IMP) {
      this._tokens.shift();
      let form2 = this._parse_formula();
      return new FImp(form1, form2);
    } else {
      return form1;
    }
  }

  _parse_variable() {
    if (this._tokens.length === 0) {
      throw new SyntaxError('La entrada termina antes de lo esperado.');
    }
    let tok = this._tokens.shift();
    if (tok instanceof Array) {
      return tok[0];
    } else {
      throw new SyntaxError('Se esperaba una variable.');
    }
  }

  _parse_atomic_formula() {
    if (this._tokens.length === 0) {
      throw new SyntaxError('La entrada termina antes de lo esperado.');
    }
    let tok = this._tokens.shift();
    if (tok instanceof Array) {
      let pred_symbol = tok[0];
      let terms = this._parse_term_list();
      return new FPred(pred_symbol, terms);
    } else if (tok === CHR_TOP) {
      return new FTrue();
    } else if (tok === CHR_BOT) {
      return new FFalse();
    } else if (tok === CHR_NEG) {
      let form = this._parse_atomic_formula();
      return new FNeg(form);
    } else if (tok === CHR_FORALL) {
      let x = this._parse_variable();
      let form = this._parse_atomic_formula();
      return new FForall(x, form);
    } else if (tok === CHR_EXISTS) {
      let x = this._parse_variable();
      let form = this._parse_atomic_formula();
      return new FExists(x, form);
    } else if (tok === '(') {
      let form = this._parse_formula();
      if (this._tokens.length == 0 || this._tokens[0] != ')') {
        throw new SyntaxError('Falta cerrar paréntesis.');
      }
      this._tokens.shift();
      return form;
    } else {
      throw new SyntaxError('Se esperaba una fórmula atómica.');
    }
  }

  _parse_term() {
    if (this._tokens.length === 0) {
      throw new SyntaxError('La entrada termina antes de lo esperado.');
    }
    let tok = this._tokens.shift();
    if (tok instanceof Array) {
      let function_symbol = tok[0];
      let terms = this._parse_term_list();
      return new Term(function_symbol, terms);
    } else {
      throw new SyntaxError('Se esperaba un término.');
    }
  }

  _parse_term_list() {
    if (this._tokens.length > 0 && this._tokens[0] === '(') {
      this._tokens.shift();
      let terms = [];
      terms.push(this._parse_term());
      while (this._tokens.length > 0 && this._tokens[0] === ',') {
        this._tokens.shift();
        terms.push(this._parse_term());
      }
      if (this._tokens.length === 0 || this._tokens[0] !== ')') {
        throw new SyntaxError('Falta cerrar paréntesis.');
      }
      this._tokens.shift();
      return terms;
    } else {
      return [];
    }
  }
}

