
/**** Reader (tokenizer and parser) ****/

var Tok_Open  = 'Tok_Open';
var Tok_Close = 'Tok_Close';
var Tok_Num   = 'Tok_Num';
var Tok_Id    = 'Tok_Id';
var Tok_EOF   = 'Tok_EOF';
var Tok_Error = 'Tok_Error';

function char_is_blank(x) {
  return x == ' ' || x == '\t' || x == '\n' || x == '\r';
}

function en(x, a, b) { return a <= x && x <= b; }

function char_is_digit(x) {
  return en(x, '0', '9') || x == '.';
}

function char_is_upper(x) {
  return en(x, 'A', 'Z') || x == '_';
}

function char_is_ident(x) {
  return en(x, '0', '9') || en(x, 'a', 'z') || en(x, 'A', 'Z') 
    || x == '_' || x == '+' || x == '-' || x == '*' || x == '/'
    || x == '<' || x == '>' || x == '=' || x == '&' || x == '|'
    || x == '^' || x == '~' || x == '!' || x == '@' || x == '#'
    || x == '$' || x == '%' || x == '{' || x == '}' || x == ':';
}

function rgb(r, g, b) {
  return {'r': r, 'g': g, 'b': b};
}

function Tokenizer(str) {
  var th = this;
  var i = 0;
  var linea = 1;

  function get_while(cond) {
      var r = '';
      while (i < str.length && cond(str[i])) {
        r += str[i];
        ++i;
      }
      return r;
  }

  th.get_token = function () {
    while (i < str.length && char_is_blank(str[i])) {
      if (str[i] == '\n') ++linea;
      ++i;
    }
    if (i >= str.length) {
      return [Tok_EOF, null];
    } else if (str[i] == '[' || str[i] == '(') {
      ++i; return [Tok_Open, null];
    } else if (str[i] == ']' || str[i] == ')') {
      ++i; return [Tok_Close, null];
    } else if (str[i] == '\\') {
      ++i; return [Tok_Id, str[i - 1]];
    } else if (char_is_digit(str[i])) {
      return [Tok_Num, get_while(char_is_digit)];
    } else if (char_is_ident(str[i])) {
      return [Tok_Id, get_while(char_is_ident)];
    } else {
      return [Tok_Error, {'programa': str, 'linea': linea, 'pos': i}];
    }
  }
}

var Parse_Ok    = 'Parse_Ok';
var Parse_Error = 'Parse_Error';
var Parse_EOF   = 'Parse_EOF';
var Parse_Error_premature_EOF = 'Parser: premature end-of-file; missing ")"';

function Parser(tokenizer) {
  var th = this;
  var tok = tokenizer.get_token();

  th.parse = function () {
    if (tok[0] == Tok_Error) {
      return [Parse_Error, tok];
    } else if (tok[0] == Tok_EOF) {
      return [Parse_EOF, null];
    } else if (tok[0] == Tok_Open) {
      var lst = [];
      tok = tokenizer.get_token();
      while (true) {
        if (tok[0] == Tok_Error) {
          return [Parse_Error, tok];
        } else if (tok[0] == Tok_Close) {
          tok = tokenizer.get_token();
          return [Parse_Ok, lst];
        } else if (tok[0] == Tok_EOF) {
          return [Parse_Error, Parse_Error_premature_EOF];
        } else {
          var e = th.parse();
          if (e[0] == Parse_Error) {
            return e;
          } else if (e[0] == Parse_EOF) {
            return [Parse_Error, Parse_Error_premature_EOF];
          } else {
            lst.push(e[1]);
          }
        }
      }
    } else if (tok[0] == Tok_Id) {
      var name = tok[1];
      tok = tokenizer.get_token();
      return [Parse_Ok, name];
    } else if (tok[0] == Tok_Num) {
      var num = tok[1];
      tok = tokenizer.get_token();

      var es_float = false;
      for (var i in num) {
        if (num[i] == '.') {
          es_float = true;
        }
      }
      if (es_float) {
        return [Parse_Ok, parseFloat(num)];
      } else {
        return [Parse_Ok, parseInt(num)];
      }
    }
  }
}

/**** Writer ****/

function is_any(x) { return true; }
function is_list(x) { return x instanceof Array; }
function is_block(x) { return is_list(x); }
function is_number(x) { return typeof(x) == 'number'; }
function is_symbol(x) { return typeof(x) == 'string'; }
function is_var(x) { return is_symbol(x) && x.length > 0 && char_is_upper(x[0]); }
function is_keyword(x) { return is_symbol(x) && x.length > 0 && x[x.length - 1] == ':'; }

function show(x) {
  var r = '';
  if (is_list(x)) {
    var sep = '';
    r += '[';
    for (i in x) {
      r += sep + show(x[i]);
      sep = ' ';
    }
    r += ']';
  } else if (is_number(x)) {
    r += x;
  } else if (is_symbol(x)) {
    r += x;
  } else {
    r += x;
  }
  return r;
}

/**** Tortuga ****/

function rad2deg(x) {
  return x * 180 / Math.PI;
}

function deg2rad(x) {
  return x * Math.PI / 180;
}

function Tortuga(canvas_id) {
  var th = this;

  var canvas = document.getElementById(canvas_id);
  var ctx = canvas.getContext('2d');
  var x, y, angle, pen_down, strokeColor;

  th.init = function () {
    x = canvas.width / 2;
    y = canvas.height / 2;
    angle = 90;
    pen_down = true;
    strokeColor = rgb(255, 0, 0);
  };

  function draw_line(x0, y0, x1, y1) {
    ctx.strokeStyle = "rgb(" + strokeColor.r + ", " + strokeColor.g + ", " + strokeColor.b + ")";
    ctx.beginPath();
    ctx.moveTo(x0, y0);
    ctx.lineTo(x1, y1);
    ctx.stroke();
    ctx.closePath();
  }

  th.state = function () {
    return [x, y, angle, pen_down, strokeColor];
  };

  th.setState = function (s) {
    x = s[0];
    y = s[1];
    angle = s[2];
    pen_down = s[3];
    strokeColor = s[4];
  };

  th.avanzar = function (k) {
    var x0 = x;
    var y0 = y;
    x += Math.cos(deg2rad(angle)) * k;
    y -= Math.sin(deg2rad(angle)) * k;
    if (pen_down) {
      draw_line(x0, y0, x, y);
    }
  };

  function wrap_angle() {
    if (angle < 0) {
      angle += 360 * Math.ceil(-angle / 360);
    } else if (angle > 360) {
      angle -= 360 * Math.floor(angle / 360);
    }
  };

  th.girar = function (a) {
    angle += a;
    wrap_angle();
  };

  th.pen_down = function () { pen_down = true; };
  th.pen_up = function () { pen_down = false; };
}

/**** Unification ****/

var last_fresh = 500;

function fresh_variable() {
  last_fresh += 1;
  return '_G' + last_fresh;
}

function copy_term(term, vars) {
  if (is_list(term)) {
    var new_term = [];
    for (i in term) {
      new_term.push(copy_term(term[i], vars));
    }
    return new_term;
  } else if (is_var(term)) {
    if (term in vars) {
      return vars[term];
    } else {
      var fresh = fresh_variable();
      vars[term] = fresh;
      return fresh;
    }
  } else {
    return term;
  }
}

function unify(set_eqs, bindings) {

  function rep(x) {
    while (x in bindings) {
      x = bindings[x];
    }
    return x;
  }

  while (set_eqs.length > 0) {
    var e = set_eqs.pop();

    var x = rep(e[0]);
    var y = rep(e[1]);

    if (is_var(x) && is_var(y) && x == y) {
      /* skip */
    } else if (is_var(x)) {
      bindings[x] = y;
    } else if (is_var(y)) {
      bindings[y] = x;
    } else if (is_list(x) && is_list(y) && x.length == y.length) {
      for (var i in x) {
        set_eqs.push([x[i], y[i]]);
      }
    } else if (typeof(x) == typeof(y)) {
      return x == y;
    } else {
      return false;
    }
  }
  return true;
}

/**** Evaluator ****/

function ordinal_for(j) {
  var ordinal;
  if (j % 10 == 1) {
    ordinal = 'st';
  } else if (j % 10 == 2) {
    ordinal = 'nd';
  } else if (j % 10 == 3) {
    ordinal = 'rd';
  } else {
    ordinal = 'th';
  }
  return ordinal;
}

var Eval_Error = 'Eval_Error';
var Eval_Error_undefined_word = 'Evaluator: undefined word';
var Eval_Error_too_few_args = 'Evaluator: too few arguments';
var Eval_Error_wrong_types = 'Evaluator: type mismatch';
var Eval_Error_zero_div = 'Evaluator: zero division';
var Eval_Error_empty_list = 'Evaluator: empty list';
var Eval_Error_lonely_end = 'Evaluator: "end" found without a keyword';

function Eval_Fail() {}

function Evaluator(id_canvas) {
  var th = this;
  var stack = [];

  var env = null;

  var tortuga = new Tortuga(id_canvas);

  tortuga.init();
  
  function init_env() {
    env = {
      /*** Arithmetic operations ***/
      '+': builtin_2_1('+', is_number, is_number, function (x, y) { return x + y; }),
      '*': builtin_2_1('*', is_number, is_number, function (x, y) { return x * y; }),
      '-': builtin_2_1('-', is_number, is_number, function (x, y) { return x - y; }),
      '/': builtin_2_1('/', is_number, is_number, function (x, y) {
          if (y == 0) {
            reportar_error(Eval_Error_zero_div);
            return Eval_Fail;
          }
          return x / y;
      }),
      '%': builtin_2_1('%', is_number, is_number, function (x, y) {
          if (y == 0) {
            reportar_error(Eval_Error_zero_div);
            return Eval_Fail;
          }
          return x % y;
      }),
      'neg': builtin_1_1('neg', is_number, function (x) { return -x; }),
      'sin': builtin_1_1('sin', is_number, function (x) { return Math.sin(deg2rad(x)); }),
      'cos': builtin_1_1('cos', is_number, function (x) { return Math.cos(deg2rad(x)); }),
      'tan': builtin_1_1('tan', is_number, function (x) { return Math.tan(deg2rad(x)); }),
      'pow': builtin_2_1('pow', is_number, is_number, function (x, y) { return Math.pow(x, y); }),

      /*** Relational operators ***/
      '==': builtin_2_1('==', is_any, is_any, function (x, y) { return x == y; }),
      '!=': builtin_2_1('!=', is_any, is_any, function (x, y) { return x != y; }),
      '<': builtin_2_1('<', is_any, is_any, function (x, y) { return x < y; }),
      '>': builtin_2_1('>', is_any, is_any, function (x, y) { return x > y; }),
      '=<': builtin_2_1('=<', is_any, is_any, function (x, y) { return x <= y; }),
      '>=': builtin_2_1('>=', is_any, is_any, function (x, y) { return x >= y; }),

      /*** Stack manipulation ***/
      'drop': builtin_1_0('drop', is_any, function (x) {}),
      'dup': builtin_1_0('dup', is_any, function (x) { stack.push(x); stack.push(x); }),
      'dip': builtin_2_0('dip', is_any, is_block, function (x, bl) {
         th.evaluar_bloque(bl);
         stack.push(x);
       }),
      'swap': builtin_2_n('swap', is_any, is_any, function (x, y) { return [y, x]; }),
      'nop': function () {},

      /*** Turtle graphics ***/
      'cls': clear_screen,
      'ad': builtin_1_0('ad', is_number, function (x) { tortuga.avanzar(x); }),
      'tr': builtin_1_0('tr', is_number, function (x) { tortuga.girar(-x); }),
      'tl': builtin_1_0('tl', is_number, function (x) { tortuga.girar(x); }),
      'up': function () { tortuga.pen_up(); },
      'down': function () { tortuga.pen_down(); },

      'pusha': function () { stack.push(tortuga.state()); },
      'popa': builtin_1_0('popa', is_any, function (s) {
        tortuga.setState(s);
       }),

      /*** List operations ***/
      'range': builtin_2_1('..', is_number, is_number, function (x, y) {
          var lst = [];
          for (var i = x; i <= y; ++i) {
            lst.push(i);
          }
          return lst;
      }),
      'cons': builtin_2_1('cons', is_any, is_list, function (x, xs) {
          var ys = [];
          ys.push(x);
          for (var i in xs) {
            ys.push(xs[i]);
          }
          return ys;
      }),
      'uncons': builtin_1_n('uncons', is_list, function (xs) {
          if (xs.length == 0) {
            reportar_error(Eval_Error_empty_list + ' trying to uncons');
            return Eval_Fail;
          }
          var ys = [];
          for (var i = 1; i < xs.length; ++i) {
            ys.push(xs[i]);
          }
          return [xs[0], ys];
      }),
      'snoc': builtin_2_1('snoc', is_list, is_any, function (xs, x) {
          var ys = [];
          for (var i in xs) {
            ys.push(xs[i]);
          }
          ys.push(x);
          return ys;
      }),
      'unsnoc': builtin_1_n('unsnoc', is_list, function (xs) {
          if (xs.length == 0) {
            reportar_error(Eval_Error_empty_list + ' trying to unsnoc');
            return Eval_Fail;
          }
          var ys = [];
          for (var i = 0; i < xs.length - 1; ++i) {
            ys.push(xs[i]);
          }
          return [ys, xs[xs.length - 1]];
      }),
      'map': builtin_2_1('map', is_list, is_block, function (xs, bl) {
          var lst = [];
          for (var i in xs) {
            stack.push(xs[i]);
            if (th.evaluar_bloque(bl) == Eval_Fail) return Eval_Fail;
            lst.push(stack.pop());
          }
          return lst;
      }),
      'each': builtin_2_0('map', is_list, is_block, function (xs, bl) {
          var lst = [];
          for (var i in xs) {
            stack.push(xs[i]);
            if (th.evaluar_bloque(bl) == Eval_Fail) return Eval_Fail;
          }
      }),
      'zip': builtin_2_1('zip', is_list, is_list, function (xs, ys) {
          var lst = [];
          var llen = Math.min(xs.length, ys.length);
          for (var i = 0; i < llen; ++i) {
            lst.push([xs[i], ys[i]]);
          }
          return lst;
      }),
      'filter': builtin_2_1('filter', is_list, is_block, function (xs, bl) {
          var lst = [];
          for (var i in xs) {
            var elem = xs[i];
            stack.push(elem);
            var r = th.evaluar_bloque(bl);
            if (r == Eval_Fail) return Eval_Fail;
            if (stack.pop()) {
              lst.push(elem);
            }
          }
          return lst;
      }),
      'zip-with': builtin_3_1('zip-with', is_list, is_list, is_block, function (xs, ys, bl) {
          var lst = [];
          var llen = Math.min(xs.length, ys.length);
          for (var i = 0; i < llen; ++i) {
            stack.push(xs[i]);
            stack.push(ys[i]);
            if (th.evaluar_bloque(bl) == Eval_Fail) return Eval_Fail;
            lst.push(stack.pop());
          }
          return lst;
      }),
      
      /*** Binding and unification ***/
      'copy-term': builtin_1_1('copy-term', is_any, function (term) {
          return copy_term(term, {});
      }),
      'unify': builtin_1_1('unify', is_list, function (term) {
          return unify_term(copy_term(term, {}));
      }),
      'let': builtin_2_0('let', is_list, is_block, function (term, bl) {
         var fresh_args = copy_term([term, bl], {});
         var term2 = fresh_args[0];
         var bl2 = fresh_args[1];
         var substitution = unify_term(term2);
         if (!substitution) {
           return;
         }
         var bl3 = copy_term(bl2, substitution);
         th.evaluar_bloque(bl3);
      }),
      'fun': builtin_2_0('fun', is_list, is_block, function (term, bl) {
          stack.push([term, bl, 'let']);
      }),
      
      /*** Animations ***/
      'apar': builtin_1_0('apar', is_list, function (blocks) {
          for (var i in blocks) {
            var faux = function (ii, i) {
              function fi () {
                clearInterval(ii);
                var ev = new Evaluator(id_canvas);
                ev.evaluar_bloque(blocks[i]);
              }
              ii = setInterval(fi, 1);
            };
            faux(null, i);
          }
      }),

      'aseq': builtin_2_0('aseq', is_block, is_number, function (bl, ntimes) {
          var interv;
          var times = 0;
          function f() {
            times += 1;
            if (times == ntimes) {
              clearInterval(interv);
              return;
            }
            th.evaluar_bloque(bl);
          }
          interv = setInterval(f, tortuga.speed);
      }),

      /*** Special syntax ***/
      'end': function () {
        var popped = [];
        while (stack.length > 0) {
          var elem = stack.pop();
          if (is_keyword(elem)) {
            for (var i in popped) {
              stack.push(popped[i]);
            }
            th.evaluar(elem.substring(0, elem.length - 1));
            return;
          }
          popped.unshift(elem);
        }
        reportar_error(Eval_Error_lonely_end);
        return Eval_Fail;
      },

      /*** Block operations ***/
      'i': builtin_1_0('i', is_block, function (bl) { th.evaluar_bloque(bl); }),
      /* Loops */
      'rep': builtin_2_0('rep', is_block, is_number, function (bl, n) {
          for (var i = 0; i < n; ++i) {
            th.evaluar_bloque(bl);
          }
       }),

      'def': builtin_2_0('def', is_symbol, is_any, function (id, x) {
          var name;
          if (is_keyword(id)) {
            name = id.substring(0, id.length - 1);
          } else {
            name = id;
          }
          env[name] = x;
       }),

       'defun': ['fun', 'def'],

       'math:pi': [Math.PI],
    };
    
    /*** aliases ***/
    aliases = {
      'av': 'ad',
      'de': 'tr',
      'iz': 'tl',
      'la': 'cls',
      'pop': 'drop',
      '**': 'pow',
    };
    for (var i in aliases) {
      env[i] = env[aliases[i]];
    }
  }

  function unify_term(term) {
    if (stack.length < term.length) {
      reportar_error(Eval_Error_too_few_args + ' for unification - expected: ' + term.length + ' got: ' + stack.length);
      return Eval_Fail;
    }
    var unif_goal = [];
    var n = term.length;
    for (var i in term) {
      var popped = stack.pop();
      unif_goal.push([term[n - i - 1], popped]);
    }
    var substitution = {};
    if (unify(unif_goal, substitution)) {
      return substitution;
    } else {
      return false;
    }
  }

  function clear_screen() {
    stack = [];
    var canvas = document.getElementById(id_canvas);
    var ctx = canvas.getContext('2d');
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    tortuga.init();
  }

  th.evaluar_bloque = function (bl) {
    for (var i in bl) {
      if (th.evaluar(bl[i]) == Eval_Fail) return Eval_Fail;
    }
  };

  th.evaluar = function (x) {
    if (is_symbol(x)) {
      if (x != '$' && x[0] == '$') {
        stack.push(x.substring(1));
        return true;
      } else if (x != ':' && x[x.length - 1] == ':') {
        stack.push(x);
        return true;
      } else if (x == '\\') {
        stack.push('fun:');
        return true;
      } else if (x in env) {
        var builtin = env[x];
        if (is_block(builtin)) {
          th.evaluar_bloque(builtin);
        } else {
          return builtin();
        }
      } else {
        reportar_error(Eval_Error_undefined_word + ' "' + x + '"');
        return Eval_Fail;
      }
    } else {
      stack.push(x);
      return true;
    }
  };

  th.dump_stack = function (max_elts) {
    var h = '';
    var downto = Math.max(0, stack.length - max_elts);
    for (var i = stack.length - 1; i >= downto; --i) {
       h += show(stack[i]) + '<br>';
    }
    return h;
  };

  function builtin_op(name, predicates, op) {
    return function () {
      if (stack.length < predicates.length) {
        reportar_error(Eval_Error_too_few_args + ' for "' + name + '" expected: ' + predicates.length + ' got: ' + stack.length);
        return Eval_Fail;
      }
      var args = [];
      var n = predicates.length;
      for (var i = 0; i < predicates.length; ++i) {
        var x = stack.pop();
        var j = n - i - 1;
        if (!predicates[j](x)) {
          ++j;
          ordinal = ordinal_for(j);
          reportar_error(Eval_Error_wrong_types + ' for "' + name + '", ' + j + ordinal + ' arg: ' + x);
          return Eval_Fail;
        }
        args.unshift(x);
      }
      var res = op(args); 
      if (res == Eval_Fail) return Eval_Fail;
      for (var i in res) {
        if (res[i] == Eval_Fail) return Eval_Fail;
        stack.push(res[i]);
      }
    };
  }

  /* builtin_n_m --> takes <n> arguments and returns <m> values */

  function builtin_1_0(name, pred, op) {
    return builtin_op(name, [pred], function (xs) { op(xs[0]); return []; });
  }

  function builtin_1_1(name, pred, op) {
    return builtin_op(name, [pred], function (xs) { return [op(xs[0])]; });
  }

  function builtin_1_n(name, pred, op) {
    return builtin_op(name, [pred], function (xs) { return op(xs[0]); });
  }

  function builtin_2_0(name, pred1, pred2, op) {
    return builtin_op(name, [pred1, pred2], function (xs) { op(xs[0], xs[1]); return []; });
  }

  function builtin_2_1(name, pred1, pred2, op) {
    return builtin_op(name, [pred1, pred2], function (xs) { return [op(xs[0], xs[1])]; });
  }

  function builtin_2_n(name, pred1, pred2, op) {
    return builtin_op(name, [pred1, pred2], function (xs) { return op(xs[0], xs[1]); });
  }

  function builtin_3_1(name, pred1, pred2, pred3, op) {
    return builtin_op(name, [pred1, pred2, pred3], function (xs) { return [op(xs[0], xs[1], xs[2])]; });
  }

  init_env();
}

/**** Error ****/

function borrar_error(error_elem) {
  error_elem.innerHTML = '';
}

function poner_error(error_elem, msg) {
  error_elem.innerHTML = msg;
}

function reportar_error(cod) {
  if (cod[0] == Tok_Error) {
    var programa = cod[1].programa;
    poner_error(__error_elem, 'Tokenizer: unknown character: "' + programa[cod[1].pos] + '", line: ' + cod[1].linea);
  } else {
    poner_error(__error_elem, cod);
  }
}

/**** Main ****/

function parse_programa(str, err_handler) {
  var parser = new Parser(new Tokenizer(str));
  var lst = [];
  while (true) {
    var pr = parser.parse();
    if (pr[0] == Parse_Error) {
      err_handler(pr[1]);
      return null;
    } else if (pr[0] == Parse_Ok) {
      lst.push(pr[1]);
    } else if (pr[0] == Parse_EOF) {
      break;
    }
  }
  return lst;
}

var Max_show_stack = 10;

function interpretar_elemento(evaluator, programa_elem, stack_elem) {
  var programa = programa_elem.value;
  function on_error(code) { 
    reportar_error(code);
    programa_elem.focus();
    programa_elem.select();
  }
  var parsed = parse_programa(programa, on_error);
  if (parsed == null) return;
  evaluator.evaluar_bloque(parsed);
  stack_elem.innerHTML = evaluator.dump_stack(Max_show_stack);
  programa_elem.focus();
  programa_elem.select();
}

/**** Init globals ****/

var __evaluator = null;
var __programa_elem = null;
var __stack_elem = null;
var __error_elem = null;
function init(id_programa, id_stack, id_canvas, id_error) {
  /*
  for (x in window) {
    document.write(x);
    document.write('<br>');
  }
  */

  __evaluator = new Evaluator(id_canvas);
  __programa_elem = document.getElementById(id_programa);
  __stack_elem = document.getElementById(id_stack);
  __error_elem = document.getElementById(id_error)

  __programa_elem.focus();
  __programa_elem.select();
}

function programa_onKeyDown() {
  if (__error_elem) {
    borrar_error(__error_elem);
  }
}

