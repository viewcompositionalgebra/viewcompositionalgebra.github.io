(function (global, factory) {
typeof exports === 'object' && typeof module !== 'undefined' ? factory(exports, require('ramda'), require('squel'), require('pg'), require('jquery'), require('sql.js')) :
typeof define === 'function' && define.amd ? define(['exports', 'ramda', 'squel', 'pg', 'jquery', 'sql.js'], factory) :
(global = global || self, factory(global.vca = global.vca || {}, global.R, global.squel, global.pg, global.$, global.sql_js));
}(this, (function (exports, R$1, squelbase, pg, $$1, sql_js) { 'use strict';

var R$1__default = 'default' in R$1 ? R$1['default'] : R$1;
$$1 = $$1 && Object.prototype.hasOwnProperty.call($$1, 'default') ? $$1['default'] : $$1;

function peg$subclass(child, parent) {
  function ctor() { this.constructor = child; }
  ctor.prototype = parent.prototype;
  child.prototype = new ctor();
}

function peg$SyntaxError(message, expected, found, location) {
  this.message  = message;
  this.expected = expected;
  this.found    = found;
  this.location = location;
  this.name     = "SyntaxError";

  if (typeof Error.captureStackTrace === "function") {
    Error.captureStackTrace(this, peg$SyntaxError);
  }
}

peg$subclass(peg$SyntaxError, Error);

peg$SyntaxError.buildMessage = function(expected, found) {
  var DESCRIBE_EXPECTATION_FNS = {
        literal: function(expectation) {
          return "\"" + literalEscape(expectation.text) + "\"";
        },

        "class": function(expectation) {
          var escapedParts = "",
              i;

          for (i = 0; i < expectation.parts.length; i++) {
            escapedParts += expectation.parts[i] instanceof Array
              ? classEscape(expectation.parts[i][0]) + "-" + classEscape(expectation.parts[i][1])
              : classEscape(expectation.parts[i]);
          }

          return "[" + (expectation.inverted ? "^" : "") + escapedParts + "]";
        },

        any: function(expectation) {
          return "any character";
        },

        end: function(expectation) {
          return "end of input";
        },

        other: function(expectation) {
          return expectation.description;
        }
      };

  function hex(ch) {
    return ch.charCodeAt(0).toString(16).toUpperCase();
  }

  function literalEscape(s) {
    return s
      .replace(/\\/g, '\\\\')
      .replace(/"/g,  '\\"')
      .replace(/\0/g, '\\0')
      .replace(/\t/g, '\\t')
      .replace(/\n/g, '\\n')
      .replace(/\r/g, '\\r')
      .replace(/[\x00-\x0F]/g,          function(ch) { return '\\x0' + hex(ch); })
      .replace(/[\x10-\x1F\x7F-\x9F]/g, function(ch) { return '\\x'  + hex(ch); });
  }

  function classEscape(s) {
    return s
      .replace(/\\/g, '\\\\')
      .replace(/\]/g, '\\]')
      .replace(/\^/g, '\\^')
      .replace(/-/g,  '\\-')
      .replace(/\0/g, '\\0')
      .replace(/\t/g, '\\t')
      .replace(/\n/g, '\\n')
      .replace(/\r/g, '\\r')
      .replace(/[\x00-\x0F]/g,          function(ch) { return '\\x0' + hex(ch); })
      .replace(/[\x10-\x1F\x7F-\x9F]/g, function(ch) { return '\\x'  + hex(ch); });
  }

  function describeExpectation(expectation) {
    return DESCRIBE_EXPECTATION_FNS[expectation.type](expectation);
  }

  function describeExpected(expected) {
    var descriptions = new Array(expected.length),
        i, j;

    for (i = 0; i < expected.length; i++) {
      descriptions[i] = describeExpectation(expected[i]);
    }

    descriptions.sort();

    if (descriptions.length > 0) {
      for (i = 1, j = 1; i < descriptions.length; i++) {
        if (descriptions[i - 1] !== descriptions[i]) {
          descriptions[j] = descriptions[i];
          j++;
        }
      }
      descriptions.length = j;
    }

    switch (descriptions.length) {
      case 1:
        return descriptions[0];

      case 2:
        return descriptions[0] + " or " + descriptions[1];

      default:
        return descriptions.slice(0, -1).join(", ")
          + ", or "
          + descriptions[descriptions.length - 1];
    }
  }

  function describeFound(found) {
    return found ? "\"" + literalEscape(found) + "\"" : "end of input";
  }

  return "Expected " + describeExpected(expected) + " but " + describeFound(found) + " found.";
};

function peg$parse(input, options) {
  options = options !== void 0 ? options : {};

  var peg$FAILED = {},

      peg$startRuleFunctions = { start: peg$parsestart },
      peg$startRuleFunction  = peg$parsestart,

      peg$c0 = function(q) { return q; },
      peg$c1 = function(g, f, w) { 
          let ops = R$1.reject(R$1.isNil, [g, w, f]);
          R$1.reduce((acc, op) => {
            acc.c = op;
            return op;
          }, ops[0], R$1.tail(ops));

          return g;
        },
      peg$c2 = function(terms) { return GroupBy(GroupBy.termsToAgbFs(terms)); },
      peg$c3 = function(n) { return Source({source: n, alias: n}); },
      peg$c4 = ",",
      peg$c5 = peg$literalExpectation(",", false),
      peg$c6 = function(head, tail) { return Where({ exprs: flatten(head, tail, 3) }) },
      peg$c7 = function(head, tail) { return flatten(head, tail, 3); },
      peg$c8 = function(e, a) { 
          if (!a) {
            if (e.classType == "Attr") 
              a = e.attr;
            else if (e.classType == "Func")
              a = "y";
            else
              throw Error(`PClause missing alias: ${e.classType}, ${e.type}, ${e.toSql()}`)
          } else {
            a = a[2];
          }
          return PClause({e, alias:a}) 
        },
      peg$c9 = function(head, tail) {
          let l = head;
          if (!tail) return l;
          return Expr({ op: tail[1], l, r:tail[3] });
        },
      peg$c10 = function(t, c) { return Attr({ table: t, attr: c }); },
      peg$c11 = function(c) { return Attr({ attr: c})},
      peg$c12 = function(x) { return Value(x) },
      peg$c13 = function(e) { return Paren({expr:e}); },
      peg$c14 = function(n, fargs) { 
          fargs = fargs || [];
          return Func({fname:n, args:fargs})
        },
      peg$c15 = function(head, tail) { return flatten(head, tail, 3) },
      peg$c16 = function(s) { 
        return s;
        },
      peg$c17 = function(digits) { 
          var x = flatstr(digits);
          if (x.indexOf('.') >= 0) {
            return { type: "Number", value: parseFloat(x)};
          }
          return { type: "Number", value :parseInt(x) };
        },
      peg$c18 = "-",
      peg$c19 = peg$literalExpectation("-", false),
      peg$c20 = "+",
      peg$c21 = peg$literalExpectation("+", false),
      peg$c27 = "||",
      peg$c28 = peg$literalExpectation("||", false),
      peg$c29 = "*",
      peg$c30 = peg$literalExpectation("*", false),
      peg$c31 = "/",
      peg$c32 = peg$literalExpectation("/", false),
      peg$c33 = "%",
      peg$c34 = peg$literalExpectation("%", false),
      peg$c35 = "<<",
      peg$c36 = peg$literalExpectation("<<", false),
      peg$c37 = ">>",
      peg$c38 = peg$literalExpectation(">>", false),
      peg$c39 = "&",
      peg$c40 = peg$literalExpectation("&", false),
      peg$c41 = "<=",
      peg$c42 = peg$literalExpectation("<=", false),
      peg$c43 = ">=",
      peg$c44 = peg$literalExpectation(">=", false),
      peg$c45 = "<",
      peg$c46 = peg$literalExpectation("<", false),
      peg$c47 = ">",
      peg$c48 = peg$literalExpectation(">", false),
      peg$c49 = "=",
      peg$c50 = peg$literalExpectation("=", false),
      peg$c51 = "==",
      peg$c52 = peg$literalExpectation("==", false),
      peg$c53 = "!=",
      peg$c54 = peg$literalExpectation("!=", false),
      peg$c55 = "<>",
      peg$c56 = peg$literalExpectation("<>", false),
      peg$c57 = "OR",
      peg$c58 = peg$literalExpectation("OR", false),
      peg$c59 = "or",
      peg$c60 = peg$literalExpectation("or", false),
      peg$c61 = "AND",
      peg$c62 = peg$literalExpectation("AND", false),
      peg$c63 = "and",
      peg$c64 = peg$literalExpectation("and", false),
      peg$c69 = /^[A-Za-z0-9_]/,
      peg$c70 = peg$classExpectation([["A", "Z"], ["a", "z"], ["0", "9"], "_"], false, false),
      peg$c71 = function(str) { return str.join('') },
      peg$c72 = "as",
      peg$c73 = peg$literalExpectation("as", true),
      peg$c74 = "select",
      peg$c75 = peg$literalExpectation("select", true),
      peg$c76 = "from",
      peg$c77 = peg$literalExpectation("FROM", true),
      peg$c78 = "where",
      peg$c79 = peg$literalExpectation("WHERE", true),
      peg$c80 = /^[ \t\n\r]/,
      peg$c81 = peg$classExpectation([" ", "\t", "\n", "\r"], false, false),
      peg$c82 = /^[0-9]/,
      peg$c83 = peg$classExpectation([["0", "9"]], false, false),
      peg$c84 = ".",
      peg$c85 = peg$literalExpectation(".", false),
      peg$c90 = "(",
      peg$c91 = peg$literalExpectation("(", false),
      peg$c92 = ")",
      peg$c93 = peg$literalExpectation(")", false),
      peg$c94 = "\n",
      peg$c95 = peg$literalExpectation("\n", false),
      peg$c96 = peg$otherExpectation("string"),
      peg$c97 = "\"",
      peg$c98 = peg$literalExpectation("\"", false),
      peg$c99 = function(chars) {
            return { type: "Literal", value: chars.join("") };
          },
      peg$c100 = "'",
      peg$c101 = peg$literalExpectation("'", false),
      peg$c102 = "\\",
      peg$c103 = peg$literalExpectation("\\", false),
      peg$c104 = function() { return text(); },
      peg$c105 = function(sequence) { return sequence; },
      peg$c106 = function() { return ""; },
      peg$c107 = "0",
      peg$c108 = peg$literalExpectation("0", false),
      peg$c109 = function() { return "\0"; },
      peg$c110 = /^[\n\r\u2028\u2029]/,
      peg$c111 = peg$classExpectation(["\n", "\r", "\u2028", "\u2029"], false, false),
      peg$c112 = peg$anyExpectation(),
      peg$c113 = "b",
      peg$c114 = peg$literalExpectation("b", false),
      peg$c115 = function() { return "\b";   },
      peg$c116 = "f",
      peg$c117 = peg$literalExpectation("f", false),
      peg$c118 = function() { return "\f";   },
      peg$c119 = "n",
      peg$c120 = peg$literalExpectation("n", false),
      peg$c121 = function() { return "\n";   },
      peg$c122 = "r",
      peg$c123 = peg$literalExpectation("r", false),
      peg$c124 = function() { return "\r";   },
      peg$c125 = "t",
      peg$c126 = peg$literalExpectation("t", false),
      peg$c127 = function() { return "\t";   },
      peg$c128 = "v",
      peg$c129 = peg$literalExpectation("v", false),
      peg$c130 = function() { return "\x0B"; },
      peg$c131 = peg$otherExpectation("end of line"),
      peg$c132 = "\r\n",
      peg$c133 = peg$literalExpectation("\r\n", false),
      peg$c134 = "\r",
      peg$c135 = peg$literalExpectation("\r", false),
      peg$c136 = "\u2028",
      peg$c137 = peg$literalExpectation("\u2028", false),
      peg$c138 = "\u2029",
      peg$c139 = peg$literalExpectation("\u2029", false),
      peg$c140 = "x",
      peg$c141 = peg$literalExpectation("x", false),
      peg$c142 = "u",
      peg$c143 = peg$literalExpectation("u", false),
      peg$c144 = function(digits) {
            return String.fromCharCode(parseInt(digits, 16));
          },
      peg$c145 = /^[0-9a-f]/i,
      peg$c146 = peg$classExpectation([["0", "9"], ["a", "f"]], false, true),

      peg$currPos          = 0,
      peg$savedPos         = 0,
      peg$posDetailsCache  = [{ line: 1, column: 1 }],
      peg$maxFailPos       = 0,
      peg$maxFailExpected  = [],
      peg$silentFails      = 0,

      peg$result;

  if ("startRule" in options) {
    if (!(options.startRule in peg$startRuleFunctions)) {
      throw new Error("Can't start parsing from rule \"" + options.startRule + "\".");
    }

    peg$startRuleFunction = peg$startRuleFunctions[options.startRule];
  }

  function text() {
    return input.substring(peg$savedPos, peg$currPos);
  }

  function peg$literalExpectation(text, ignoreCase) {
    return { type: "literal", text: text, ignoreCase: ignoreCase };
  }

  function peg$classExpectation(parts, inverted, ignoreCase) {
    return { type: "class", parts: parts, inverted: inverted, ignoreCase: ignoreCase };
  }

  function peg$anyExpectation() {
    return { type: "any" };
  }

  function peg$endExpectation() {
    return { type: "end" };
  }

  function peg$otherExpectation(description) {
    return { type: "other", description: description };
  }

  function peg$computePosDetails(pos) {
    var details = peg$posDetailsCache[pos], p;

    if (details) {
      return details;
    } else {
      p = pos - 1;
      while (!peg$posDetailsCache[p]) {
        p--;
      }

      details = peg$posDetailsCache[p];
      details = {
        line:   details.line,
        column: details.column
      };

      while (p < pos) {
        if (input.charCodeAt(p) === 10) {
          details.line++;
          details.column = 1;
        } else {
          details.column++;
        }

        p++;
      }

      peg$posDetailsCache[pos] = details;
      return details;
    }
  }

  function peg$computeLocation(startPos, endPos) {
    var startPosDetails = peg$computePosDetails(startPos),
        endPosDetails   = peg$computePosDetails(endPos);

    return {
      start: {
        offset: startPos,
        line:   startPosDetails.line,
        column: startPosDetails.column
      },
      end: {
        offset: endPos,
        line:   endPosDetails.line,
        column: endPosDetails.column
      }
    };
  }

  function peg$fail(expected) {
    if (peg$currPos < peg$maxFailPos) { return; }

    if (peg$currPos > peg$maxFailPos) {
      peg$maxFailPos = peg$currPos;
      peg$maxFailExpected = [];
    }

    peg$maxFailExpected.push(expected);
  }

  function peg$buildStructuredError(expected, found, location) {
    return new peg$SyntaxError(
      peg$SyntaxError.buildMessage(expected, found),
      expected,
      found,
      location
    );
  }

  function peg$parsestart() {
    var s0;

    s0 = peg$parsequery();
    if (s0 === peg$FAILED) {
      s0 = peg$parseexpr();
    }

    return s0;
  }

  function peg$parsequery() {
    var s0, s1, s2, s3;

    s0 = peg$currPos;
    s1 = peg$parsews();
    if (s1 !== peg$FAILED) {
      s2 = peg$parseQ();
      if (s2 !== peg$FAILED) {
        s3 = peg$parsews();
        if (s3 !== peg$FAILED) {
          peg$savedPos = s0;
          s1 = peg$c0(s2);
          s0 = s1;
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }

    return s0;
  }

  function peg$parseQ() {
    var s0, s1, s2, s3;

    s0 = peg$currPos;
    s1 = peg$parsegroupby();
    if (s1 !== peg$FAILED) {
      s2 = peg$parsefrom();
      if (s2 !== peg$FAILED) {
        s3 = peg$parsewhere();
        if (s3 === peg$FAILED) {
          s3 = null;
        }
        if (s3 !== peg$FAILED) {
          peg$savedPos = s0;
          s1 = peg$c1(s1, s2, s3);
          s0 = s1;
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }

    return s0;
  }

  function peg$parsegroupby() {
    var s0, s1, s2;

    s0 = peg$currPos;
    s1 = peg$parseSELECT();
    if (s1 !== peg$FAILED) {
      s2 = peg$parsegbterms();
      if (s2 !== peg$FAILED) {
        peg$savedPos = s0;
        s1 = peg$c2(s2);
        s0 = s1;
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }

    return s0;
  }

  function peg$parsefrom() {
    var s0, s1, s2, s3;

    s0 = peg$currPos;
    s1 = peg$parseFROM();
    if (s1 !== peg$FAILED) {
      s2 = peg$parsewsp();
      if (s2 !== peg$FAILED) {
        s3 = peg$parsename();
        if (s3 !== peg$FAILED) {
          peg$savedPos = s0;
          s1 = peg$c3(s3);
          s0 = s1;
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }

    return s0;
  }

  function peg$parsewhere() {
    var s0, s1, s2, s3, s4, s5, s6, s7, s8, s9;

    s0 = peg$currPos;
    s1 = peg$parseWHERE();
    if (s1 !== peg$FAILED) {
      s2 = peg$parsewsp();
      if (s2 !== peg$FAILED) {
        s3 = peg$parseexpr();
        if (s3 !== peg$FAILED) {
          s4 = [];
          s5 = peg$currPos;
          s6 = peg$parsews();
          if (s6 !== peg$FAILED) {
            if (input.charCodeAt(peg$currPos) === 44) {
              s7 = peg$c4;
              peg$currPos++;
            } else {
              s7 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c5); }
            }
            if (s7 !== peg$FAILED) {
              s8 = peg$parsews();
              if (s8 !== peg$FAILED) {
                s9 = peg$parseexpr();
                if (s9 !== peg$FAILED) {
                  s6 = [s6, s7, s8, s9];
                  s5 = s6;
                } else {
                  peg$currPos = s5;
                  s5 = peg$FAILED;
                }
              } else {
                peg$currPos = s5;
                s5 = peg$FAILED;
              }
            } else {
              peg$currPos = s5;
              s5 = peg$FAILED;
            }
          } else {
            peg$currPos = s5;
            s5 = peg$FAILED;
          }
          while (s5 !== peg$FAILED) {
            s4.push(s5);
            s5 = peg$currPos;
            s6 = peg$parsews();
            if (s6 !== peg$FAILED) {
              if (input.charCodeAt(peg$currPos) === 44) {
                s7 = peg$c4;
                peg$currPos++;
              } else {
                s7 = peg$FAILED;
                if (peg$silentFails === 0) { peg$fail(peg$c5); }
              }
              if (s7 !== peg$FAILED) {
                s8 = peg$parsews();
                if (s8 !== peg$FAILED) {
                  s9 = peg$parseexpr();
                  if (s9 !== peg$FAILED) {
                    s6 = [s6, s7, s8, s9];
                    s5 = s6;
                  } else {
                    peg$currPos = s5;
                    s5 = peg$FAILED;
                  }
                } else {
                  peg$currPos = s5;
                  s5 = peg$FAILED;
                }
              } else {
                peg$currPos = s5;
                s5 = peg$FAILED;
              }
            } else {
              peg$currPos = s5;
              s5 = peg$FAILED;
            }
          }
          if (s4 !== peg$FAILED) {
            peg$savedPos = s0;
            s1 = peg$c6(s3, s4);
            s0 = s1;
          } else {
            peg$currPos = s0;
            s0 = peg$FAILED;
          }
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }

    return s0;
  }

  function peg$parsegbterms() {
    var s0, s1, s2, s3, s4, s5, s6, s7, s8;

    s0 = peg$currPos;
    s1 = peg$parsewsp();
    if (s1 !== peg$FAILED) {
      s2 = peg$parsepclause();
      if (s2 !== peg$FAILED) {
        s3 = [];
        s4 = peg$currPos;
        s5 = peg$parsews();
        if (s5 !== peg$FAILED) {
          if (input.charCodeAt(peg$currPos) === 44) {
            s6 = peg$c4;
            peg$currPos++;
          } else {
            s6 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c5); }
          }
          if (s6 !== peg$FAILED) {
            s7 = peg$parsews();
            if (s7 !== peg$FAILED) {
              s8 = peg$parsepclause();
              if (s8 !== peg$FAILED) {
                s5 = [s5, s6, s7, s8];
                s4 = s5;
              } else {
                peg$currPos = s4;
                s4 = peg$FAILED;
              }
            } else {
              peg$currPos = s4;
              s4 = peg$FAILED;
            }
          } else {
            peg$currPos = s4;
            s4 = peg$FAILED;
          }
        } else {
          peg$currPos = s4;
          s4 = peg$FAILED;
        }
        while (s4 !== peg$FAILED) {
          s3.push(s4);
          s4 = peg$currPos;
          s5 = peg$parsews();
          if (s5 !== peg$FAILED) {
            if (input.charCodeAt(peg$currPos) === 44) {
              s6 = peg$c4;
              peg$currPos++;
            } else {
              s6 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c5); }
            }
            if (s6 !== peg$FAILED) {
              s7 = peg$parsews();
              if (s7 !== peg$FAILED) {
                s8 = peg$parsepclause();
                if (s8 !== peg$FAILED) {
                  s5 = [s5, s6, s7, s8];
                  s4 = s5;
                } else {
                  peg$currPos = s4;
                  s4 = peg$FAILED;
                }
              } else {
                peg$currPos = s4;
                s4 = peg$FAILED;
              }
            } else {
              peg$currPos = s4;
              s4 = peg$FAILED;
            }
          } else {
            peg$currPos = s4;
            s4 = peg$FAILED;
          }
        }
        if (s3 !== peg$FAILED) {
          peg$savedPos = s0;
          s1 = peg$c7(s2, s3);
          s0 = s1;
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }

    return s0;
  }

  function peg$parsepclause() {
    var s0, s1, s2, s3, s4, s5;

    s0 = peg$currPos;
    s1 = peg$parseexpr();
    if (s1 !== peg$FAILED) {
      s2 = peg$currPos;
      s3 = peg$parseAS();
      if (s3 !== peg$FAILED) {
        s4 = peg$parsewsp();
        if (s4 !== peg$FAILED) {
          s5 = peg$parsename();
          if (s5 !== peg$FAILED) {
            s3 = [s3, s4, s5];
            s2 = s3;
          } else {
            peg$currPos = s2;
            s2 = peg$FAILED;
          }
        } else {
          peg$currPos = s2;
          s2 = peg$FAILED;
        }
      } else {
        peg$currPos = s2;
        s2 = peg$FAILED;
      }
      if (s2 === peg$FAILED) {
        s2 = null;
      }
      if (s2 !== peg$FAILED) {
        peg$savedPos = s0;
        s1 = peg$c8(s1, s2);
        s0 = s1;
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }

    return s0;
  }

  function peg$parseexpr() {
    var s0, s1, s2, s3, s4, s5, s6;

    s0 = peg$currPos;
    s1 = peg$parsevalue();
    if (s1 !== peg$FAILED) {
      s2 = peg$currPos;
      s3 = peg$parsews();
      if (s3 !== peg$FAILED) {
        s4 = peg$parsebinary_operator();
        if (s4 !== peg$FAILED) {
          s5 = peg$parsews();
          if (s5 !== peg$FAILED) {
            s6 = peg$parseexpr();
            if (s6 !== peg$FAILED) {
              s3 = [s3, s4, s5, s6];
              s2 = s3;
            } else {
              peg$currPos = s2;
              s2 = peg$FAILED;
            }
          } else {
            peg$currPos = s2;
            s2 = peg$FAILED;
          }
        } else {
          peg$currPos = s2;
          s2 = peg$FAILED;
        }
      } else {
        peg$currPos = s2;
        s2 = peg$FAILED;
      }
      if (s2 === peg$FAILED) {
        s2 = null;
      }
      if (s2 !== peg$FAILED) {
        peg$savedPos = s0;
        s1 = peg$c9(s1, s2);
        s0 = s1;
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }

    return s0;
  }

  function peg$parsevalue() {
    var s0, s1, s2, s3;

    s0 = peg$parsefcall();
    if (s0 === peg$FAILED) {
      s0 = peg$parseliteral_value();
      if (s0 === peg$FAILED) {
        s0 = peg$parseparen_value();
        if (s0 === peg$FAILED) {
          s0 = peg$currPos;
          s1 = peg$parsename();
          if (s1 !== peg$FAILED) {
            s2 = peg$parsedot();
            if (s2 !== peg$FAILED) {
              s3 = peg$parsename();
              if (s3 !== peg$FAILED) {
                peg$savedPos = s0;
                s1 = peg$c10(s1, s3);
                s0 = s1;
              } else {
                peg$currPos = s0;
                s0 = peg$FAILED;
              }
            } else {
              peg$currPos = s0;
              s0 = peg$FAILED;
            }
          } else {
            peg$currPos = s0;
            s0 = peg$FAILED;
          }
          if (s0 === peg$FAILED) {
            s0 = peg$currPos;
            s1 = peg$parsename();
            if (s1 !== peg$FAILED) {
              peg$savedPos = s0;
              s1 = peg$c11(s1);
            }
            s0 = s1;
          }
        }
      }
    }

    return s0;
  }

  function peg$parseliteral_value() {
    var s0, s1;

    s0 = peg$currPos;
    s1 = peg$parsenumeric_literal();
    if (s1 === peg$FAILED) {
      s1 = peg$parsestring_literal();
    }
    if (s1 !== peg$FAILED) {
      peg$savedPos = s0;
      s1 = peg$c12(s1);
    }
    s0 = s1;

    return s0;
  }

  function peg$parseparen_value() {
    var s0, s1, s2, s3, s4, s5;

    s0 = peg$currPos;
    s1 = peg$parselparen();
    if (s1 !== peg$FAILED) {
      s2 = peg$parsews();
      if (s2 !== peg$FAILED) {
        s3 = peg$parseexpr();
        if (s3 !== peg$FAILED) {
          s4 = peg$parsews();
          if (s4 !== peg$FAILED) {
            s5 = peg$parserparen();
            if (s5 !== peg$FAILED) {
              peg$savedPos = s0;
              s1 = peg$c13(s3);
              s0 = s1;
            } else {
              peg$currPos = s0;
              s0 = peg$FAILED;
            }
          } else {
            peg$currPos = s0;
            s0 = peg$FAILED;
          }
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }

    return s0;
  }

  function peg$parsefcall() {
    var s0, s1, s2, s3, s4, s5, s6;

    s0 = peg$currPos;
    s1 = peg$parsename();
    if (s1 !== peg$FAILED) {
      s2 = peg$parsews();
      if (s2 !== peg$FAILED) {
        s3 = peg$parselparen();
        if (s3 !== peg$FAILED) {
          s4 = peg$parsefargs();
          if (s4 === peg$FAILED) {
            s4 = null;
          }
          if (s4 !== peg$FAILED) {
            s5 = peg$parsews();
            if (s5 !== peg$FAILED) {
              s6 = peg$parserparen();
              if (s6 !== peg$FAILED) {
                peg$savedPos = s0;
                s1 = peg$c14(s1, s4);
                s0 = s1;
              } else {
                peg$currPos = s0;
                s0 = peg$FAILED;
              }
            } else {
              peg$currPos = s0;
              s0 = peg$FAILED;
            }
          } else {
            peg$currPos = s0;
            s0 = peg$FAILED;
          }
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }

    return s0;
  }

  function peg$parsefargs() {
    var s0, s1, s2, s3, s4, s5, s6, s7;

    s0 = peg$currPos;
    s1 = peg$parseexpr();
    if (s1 !== peg$FAILED) {
      s2 = [];
      s3 = peg$currPos;
      s4 = peg$parsews();
      if (s4 !== peg$FAILED) {
        if (input.charCodeAt(peg$currPos) === 44) {
          s5 = peg$c4;
          peg$currPos++;
        } else {
          s5 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c5); }
        }
        if (s5 !== peg$FAILED) {
          s6 = peg$parsews();
          if (s6 !== peg$FAILED) {
            s7 = peg$parseexpr();
            if (s7 !== peg$FAILED) {
              s4 = [s4, s5, s6, s7];
              s3 = s4;
            } else {
              peg$currPos = s3;
              s3 = peg$FAILED;
            }
          } else {
            peg$currPos = s3;
            s3 = peg$FAILED;
          }
        } else {
          peg$currPos = s3;
          s3 = peg$FAILED;
        }
      } else {
        peg$currPos = s3;
        s3 = peg$FAILED;
      }
      while (s3 !== peg$FAILED) {
        s2.push(s3);
        s3 = peg$currPos;
        s4 = peg$parsews();
        if (s4 !== peg$FAILED) {
          if (input.charCodeAt(peg$currPos) === 44) {
            s5 = peg$c4;
            peg$currPos++;
          } else {
            s5 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c5); }
          }
          if (s5 !== peg$FAILED) {
            s6 = peg$parsews();
            if (s6 !== peg$FAILED) {
              s7 = peg$parseexpr();
              if (s7 !== peg$FAILED) {
                s4 = [s4, s5, s6, s7];
                s3 = s4;
              } else {
                peg$currPos = s3;
                s3 = peg$FAILED;
              }
            } else {
              peg$currPos = s3;
              s3 = peg$FAILED;
            }
          } else {
            peg$currPos = s3;
            s3 = peg$FAILED;
          }
        } else {
          peg$currPos = s3;
          s3 = peg$FAILED;
        }
      }
      if (s2 !== peg$FAILED) {
        peg$savedPos = s0;
        s1 = peg$c15(s1, s2);
        s0 = s1;
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }

    return s0;
  }

  function peg$parsestring_literal() {
    var s0, s1;

    s0 = peg$currPos;
    s1 = peg$parsejs_string_literal();
    if (s1 !== peg$FAILED) {
      peg$savedPos = s0;
      s1 = peg$c16(s1);
    }
    s0 = s1;

    return s0;
  }

  function peg$parsenumeric_literal() {
    var s0, s1, s2, s3, s4, s5, s6, s7, s8;

    s0 = peg$currPos;
    s1 = peg$currPos;
    s2 = peg$parseplus();
    if (s2 === peg$FAILED) {
      s2 = peg$parseminus();
    }
    if (s2 === peg$FAILED) {
      s2 = null;
    }
    if (s2 !== peg$FAILED) {
      s3 = peg$currPos;
      s4 = [];
      s5 = peg$parsedigit();
      if (s5 !== peg$FAILED) {
        while (s5 !== peg$FAILED) {
          s4.push(s5);
          s5 = peg$parsedigit();
        }
      } else {
        s4 = peg$FAILED;
      }
      if (s4 !== peg$FAILED) {
        s5 = peg$currPos;
        s6 = peg$parsedot();
        if (s6 !== peg$FAILED) {
          s7 = [];
          s8 = peg$parsedigit();
          if (s8 !== peg$FAILED) {
            while (s8 !== peg$FAILED) {
              s7.push(s8);
              s8 = peg$parsedigit();
            }
          } else {
            s7 = peg$FAILED;
          }
          if (s7 !== peg$FAILED) {
            s6 = [s6, s7];
            s5 = s6;
          } else {
            peg$currPos = s5;
            s5 = peg$FAILED;
          }
        } else {
          peg$currPos = s5;
          s5 = peg$FAILED;
        }
        if (s5 === peg$FAILED) {
          s5 = null;
        }
        if (s5 !== peg$FAILED) {
          s4 = [s4, s5];
          s3 = s4;
        } else {
          peg$currPos = s3;
          s3 = peg$FAILED;
        }
      } else {
        peg$currPos = s3;
        s3 = peg$FAILED;
      }
      if (s3 === peg$FAILED) {
        s3 = peg$currPos;
        s4 = peg$parsedot();
        if (s4 !== peg$FAILED) {
          s5 = [];
          s6 = peg$parsedigit();
          if (s6 !== peg$FAILED) {
            while (s6 !== peg$FAILED) {
              s5.push(s6);
              s6 = peg$parsedigit();
            }
          } else {
            s5 = peg$FAILED;
          }
          if (s5 !== peg$FAILED) {
            s4 = [s4, s5];
            s3 = s4;
          } else {
            peg$currPos = s3;
            s3 = peg$FAILED;
          }
        } else {
          peg$currPos = s3;
          s3 = peg$FAILED;
        }
      }
      if (s3 !== peg$FAILED) {
        s2 = [s2, s3];
        s1 = s2;
      } else {
        peg$currPos = s1;
        s1 = peg$FAILED;
      }
    } else {
      peg$currPos = s1;
      s1 = peg$FAILED;
    }
    if (s1 !== peg$FAILED) {
      peg$savedPos = s0;
      s1 = peg$c17(s1);
    }
    s0 = s1;

    return s0;
  }

  function peg$parsebinary_operator() {
    var s0;

    if (input.substr(peg$currPos, 2) === peg$c27) {
      s0 = peg$c27;
      peg$currPos += 2;
    } else {
      s0 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c28); }
    }
    if (s0 === peg$FAILED) {
      if (input.charCodeAt(peg$currPos) === 42) {
        s0 = peg$c29;
        peg$currPos++;
      } else {
        s0 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c30); }
      }
      if (s0 === peg$FAILED) {
        if (input.charCodeAt(peg$currPos) === 47) {
          s0 = peg$c31;
          peg$currPos++;
        } else {
          s0 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c32); }
        }
        if (s0 === peg$FAILED) {
          if (input.charCodeAt(peg$currPos) === 37) {
            s0 = peg$c33;
            peg$currPos++;
          } else {
            s0 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c34); }
          }
          if (s0 === peg$FAILED) {
            if (input.charCodeAt(peg$currPos) === 43) {
              s0 = peg$c20;
              peg$currPos++;
            } else {
              s0 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c21); }
            }
            if (s0 === peg$FAILED) {
              if (input.charCodeAt(peg$currPos) === 45) {
                s0 = peg$c18;
                peg$currPos++;
              } else {
                s0 = peg$FAILED;
                if (peg$silentFails === 0) { peg$fail(peg$c19); }
              }
              if (s0 === peg$FAILED) {
                if (input.substr(peg$currPos, 2) === peg$c35) {
                  s0 = peg$c35;
                  peg$currPos += 2;
                } else {
                  s0 = peg$FAILED;
                  if (peg$silentFails === 0) { peg$fail(peg$c36); }
                }
                if (s0 === peg$FAILED) {
                  if (input.substr(peg$currPos, 2) === peg$c37) {
                    s0 = peg$c37;
                    peg$currPos += 2;
                  } else {
                    s0 = peg$FAILED;
                    if (peg$silentFails === 0) { peg$fail(peg$c38); }
                  }
                  if (s0 === peg$FAILED) {
                    if (input.charCodeAt(peg$currPos) === 38) {
                      s0 = peg$c39;
                      peg$currPos++;
                    } else {
                      s0 = peg$FAILED;
                      if (peg$silentFails === 0) { peg$fail(peg$c40); }
                    }
                    if (s0 === peg$FAILED) {
                      if (input.substr(peg$currPos, 2) === peg$c41) {
                        s0 = peg$c41;
                        peg$currPos += 2;
                      } else {
                        s0 = peg$FAILED;
                        if (peg$silentFails === 0) { peg$fail(peg$c42); }
                      }
                      if (s0 === peg$FAILED) {
                        if (input.substr(peg$currPos, 2) === peg$c43) {
                          s0 = peg$c43;
                          peg$currPos += 2;
                        } else {
                          s0 = peg$FAILED;
                          if (peg$silentFails === 0) { peg$fail(peg$c44); }
                        }
                        if (s0 === peg$FAILED) {
                          if (input.charCodeAt(peg$currPos) === 60) {
                            s0 = peg$c45;
                            peg$currPos++;
                          } else {
                            s0 = peg$FAILED;
                            if (peg$silentFails === 0) { peg$fail(peg$c46); }
                          }
                          if (s0 === peg$FAILED) {
                            if (input.charCodeAt(peg$currPos) === 62) {
                              s0 = peg$c47;
                              peg$currPos++;
                            } else {
                              s0 = peg$FAILED;
                              if (peg$silentFails === 0) { peg$fail(peg$c48); }
                            }
                            if (s0 === peg$FAILED) {
                              if (input.charCodeAt(peg$currPos) === 61) {
                                s0 = peg$c49;
                                peg$currPos++;
                              } else {
                                s0 = peg$FAILED;
                                if (peg$silentFails === 0) { peg$fail(peg$c50); }
                              }
                              if (s0 === peg$FAILED) {
                                if (input.substr(peg$currPos, 2) === peg$c51) {
                                  s0 = peg$c51;
                                  peg$currPos += 2;
                                } else {
                                  s0 = peg$FAILED;
                                  if (peg$silentFails === 0) { peg$fail(peg$c52); }
                                }
                                if (s0 === peg$FAILED) {
                                  if (input.substr(peg$currPos, 2) === peg$c53) {
                                    s0 = peg$c53;
                                    peg$currPos += 2;
                                  } else {
                                    s0 = peg$FAILED;
                                    if (peg$silentFails === 0) { peg$fail(peg$c54); }
                                  }
                                  if (s0 === peg$FAILED) {
                                    if (input.substr(peg$currPos, 2) === peg$c55) {
                                      s0 = peg$c55;
                                      peg$currPos += 2;
                                    } else {
                                      s0 = peg$FAILED;
                                      if (peg$silentFails === 0) { peg$fail(peg$c56); }
                                    }
                                    if (s0 === peg$FAILED) {
                                      if (input.substr(peg$currPos, 2) === peg$c57) {
                                        s0 = peg$c57;
                                        peg$currPos += 2;
                                      } else {
                                        s0 = peg$FAILED;
                                        if (peg$silentFails === 0) { peg$fail(peg$c58); }
                                      }
                                      if (s0 === peg$FAILED) {
                                        if (input.substr(peg$currPos, 2) === peg$c59) {
                                          s0 = peg$c59;
                                          peg$currPos += 2;
                                        } else {
                                          s0 = peg$FAILED;
                                          if (peg$silentFails === 0) { peg$fail(peg$c60); }
                                        }
                                        if (s0 === peg$FAILED) {
                                          if (input.substr(peg$currPos, 3) === peg$c61) {
                                            s0 = peg$c61;
                                            peg$currPos += 3;
                                          } else {
                                            s0 = peg$FAILED;
                                            if (peg$silentFails === 0) { peg$fail(peg$c62); }
                                          }
                                          if (s0 === peg$FAILED) {
                                            if (input.substr(peg$currPos, 3) === peg$c63) {
                                              s0 = peg$c63;
                                              peg$currPos += 3;
                                            } else {
                                              s0 = peg$FAILED;
                                              if (peg$silentFails === 0) { peg$fail(peg$c64); }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }

    return s0;
  }

  function peg$parsename() {
    var s0, s1, s2;

    s0 = peg$currPos;
    s1 = [];
    if (peg$c69.test(input.charAt(peg$currPos))) {
      s2 = input.charAt(peg$currPos);
      peg$currPos++;
    } else {
      s2 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c70); }
    }
    if (s2 !== peg$FAILED) {
      while (s2 !== peg$FAILED) {
        s1.push(s2);
        if (peg$c69.test(input.charAt(peg$currPos))) {
          s2 = input.charAt(peg$currPos);
          peg$currPos++;
        } else {
          s2 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c70); }
        }
      }
    } else {
      s1 = peg$FAILED;
    }
    if (s1 !== peg$FAILED) {
      peg$savedPos = s0;
      s1 = peg$c71(s1);
    }
    s0 = s1;

    return s0;
  }

  function peg$parseAS() {
    var s0, s1, s2;

    s0 = peg$currPos;
    s1 = peg$parsewsp();
    if (s1 !== peg$FAILED) {
      if (input.substr(peg$currPos, 2).toLowerCase() === peg$c72) {
        s2 = input.substr(peg$currPos, 2);
        peg$currPos += 2;
      } else {
        s2 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c73); }
      }
      if (s2 !== peg$FAILED) {
        s1 = [s1, s2];
        s0 = s1;
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }

    return s0;
  }

  function peg$parseSELECT() {
    var s0;

    if (input.substr(peg$currPos, 6).toLowerCase() === peg$c74) {
      s0 = input.substr(peg$currPos, 6);
      peg$currPos += 6;
    } else {
      s0 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c75); }
    }

    return s0;
  }

  function peg$parseFROM() {
    var s0, s1, s2;

    s0 = peg$currPos;
    s1 = peg$parsewsp();
    if (s1 !== peg$FAILED) {
      if (input.substr(peg$currPos, 4).toLowerCase() === peg$c76) {
        s2 = input.substr(peg$currPos, 4);
        peg$currPos += 4;
      } else {
        s2 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c77); }
      }
      if (s2 !== peg$FAILED) {
        s1 = [s1, s2];
        s0 = s1;
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }

    return s0;
  }

  function peg$parseWHERE() {
    var s0, s1, s2;

    s0 = peg$currPos;
    s1 = peg$parsewsp();
    if (s1 !== peg$FAILED) {
      if (input.substr(peg$currPos, 5).toLowerCase() === peg$c78) {
        s2 = input.substr(peg$currPos, 5);
        peg$currPos += 5;
      } else {
        s2 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c79); }
      }
      if (s2 !== peg$FAILED) {
        s1 = [s1, s2];
        s0 = s1;
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }

    return s0;
  }

  function peg$parsews() {
    var s0, s1;

    s0 = [];
    if (peg$c80.test(input.charAt(peg$currPos))) {
      s1 = input.charAt(peg$currPos);
      peg$currPos++;
    } else {
      s1 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c81); }
    }
    while (s1 !== peg$FAILED) {
      s0.push(s1);
      if (peg$c80.test(input.charAt(peg$currPos))) {
        s1 = input.charAt(peg$currPos);
        peg$currPos++;
      } else {
        s1 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c81); }
      }
    }

    return s0;
  }

  function peg$parsewsp() {
    var s0, s1;

    s0 = [];
    if (peg$c80.test(input.charAt(peg$currPos))) {
      s1 = input.charAt(peg$currPos);
      peg$currPos++;
    } else {
      s1 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c81); }
    }
    if (s1 !== peg$FAILED) {
      while (s1 !== peg$FAILED) {
        s0.push(s1);
        if (peg$c80.test(input.charAt(peg$currPos))) {
          s1 = input.charAt(peg$currPos);
          peg$currPos++;
        } else {
          s1 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c81); }
        }
      }
    } else {
      s0 = peg$FAILED;
    }

    return s0;
  }

  function peg$parsedigit() {
    var s0;

    if (peg$c82.test(input.charAt(peg$currPos))) {
      s0 = input.charAt(peg$currPos);
      peg$currPos++;
    } else {
      s0 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c83); }
    }

    return s0;
  }

  function peg$parsedot() {
    var s0;

    if (input.charCodeAt(peg$currPos) === 46) {
      s0 = peg$c84;
      peg$currPos++;
    } else {
      s0 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c85); }
    }

    return s0;
  }

  function peg$parseminus() {
    var s0;

    if (input.charCodeAt(peg$currPos) === 45) {
      s0 = peg$c18;
      peg$currPos++;
    } else {
      s0 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c19); }
    }

    return s0;
  }

  function peg$parseplus() {
    var s0;

    if (input.charCodeAt(peg$currPos) === 43) {
      s0 = peg$c20;
      peg$currPos++;
    } else {
      s0 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c21); }
    }

    return s0;
  }

  function peg$parselparen() {
    var s0;

    if (input.charCodeAt(peg$currPos) === 40) {
      s0 = peg$c90;
      peg$currPos++;
    } else {
      s0 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c91); }
    }

    return s0;
  }

  function peg$parserparen() {
    var s0;

    if (input.charCodeAt(peg$currPos) === 41) {
      s0 = peg$c92;
      peg$currPos++;
    } else {
      s0 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c93); }
    }

    return s0;
  }

  function peg$parsejs_string_literal() {
    var s0, s1, s2, s3;

    peg$silentFails++;
    s0 = peg$currPos;
    if (input.charCodeAt(peg$currPos) === 34) {
      s1 = peg$c97;
      peg$currPos++;
    } else {
      s1 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c98); }
    }
    if (s1 !== peg$FAILED) {
      s2 = [];
      s3 = peg$parsejs_double_string_character();
      while (s3 !== peg$FAILED) {
        s2.push(s3);
        s3 = peg$parsejs_double_string_character();
      }
      if (s2 !== peg$FAILED) {
        if (input.charCodeAt(peg$currPos) === 34) {
          s3 = peg$c97;
          peg$currPos++;
        } else {
          s3 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c98); }
        }
        if (s3 !== peg$FAILED) {
          peg$savedPos = s0;
          s1 = peg$c99(s2);
          s0 = s1;
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }
    if (s0 === peg$FAILED) {
      s0 = peg$currPos;
      if (input.charCodeAt(peg$currPos) === 39) {
        s1 = peg$c100;
        peg$currPos++;
      } else {
        s1 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c101); }
      }
      if (s1 !== peg$FAILED) {
        s2 = [];
        s3 = peg$parsejs_single_string_character();
        while (s3 !== peg$FAILED) {
          s2.push(s3);
          s3 = peg$parsejs_single_string_character();
        }
        if (s2 !== peg$FAILED) {
          if (input.charCodeAt(peg$currPos) === 39) {
            s3 = peg$c100;
            peg$currPos++;
          } else {
            s3 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c101); }
          }
          if (s3 !== peg$FAILED) {
            peg$savedPos = s0;
            s1 = peg$c99(s2);
            s0 = s1;
          } else {
            peg$currPos = s0;
            s0 = peg$FAILED;
          }
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    }
    peg$silentFails--;
    if (s0 === peg$FAILED) {
      s1 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c96); }
    }

    return s0;
  }

  function peg$parsejs_double_string_character() {
    var s0, s1, s2;

    s0 = peg$currPos;
    s1 = peg$currPos;
    peg$silentFails++;
    if (input.charCodeAt(peg$currPos) === 34) {
      s2 = peg$c97;
      peg$currPos++;
    } else {
      s2 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c98); }
    }
    if (s2 === peg$FAILED) {
      if (input.charCodeAt(peg$currPos) === 92) {
        s2 = peg$c102;
        peg$currPos++;
      } else {
        s2 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c103); }
      }
      if (s2 === peg$FAILED) {
        s2 = peg$parsejs_line_terminator();
      }
    }
    peg$silentFails--;
    if (s2 === peg$FAILED) {
      s1 = void 0;
    } else {
      peg$currPos = s1;
      s1 = peg$FAILED;
    }
    if (s1 !== peg$FAILED) {
      s2 = peg$parsejs_source_character();
      if (s2 !== peg$FAILED) {
        peg$savedPos = s0;
        s1 = peg$c104();
        s0 = s1;
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }
    if (s0 === peg$FAILED) {
      s0 = peg$currPos;
      if (input.charCodeAt(peg$currPos) === 92) {
        s1 = peg$c102;
        peg$currPos++;
      } else {
        s1 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c103); }
      }
      if (s1 !== peg$FAILED) {
        s2 = peg$parsejs_escape_sequence();
        if (s2 !== peg$FAILED) {
          peg$savedPos = s0;
          s1 = peg$c105(s2);
          s0 = s1;
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
      if (s0 === peg$FAILED) {
        s0 = peg$parsejs_line_continuation();
      }
    }

    return s0;
  }

  function peg$parsejs_single_string_character() {
    var s0, s1, s2;

    s0 = peg$currPos;
    s1 = peg$currPos;
    peg$silentFails++;
    if (input.charCodeAt(peg$currPos) === 39) {
      s2 = peg$c100;
      peg$currPos++;
    } else {
      s2 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c101); }
    }
    if (s2 === peg$FAILED) {
      if (input.charCodeAt(peg$currPos) === 92) {
        s2 = peg$c102;
        peg$currPos++;
      } else {
        s2 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c103); }
      }
      if (s2 === peg$FAILED) {
        s2 = peg$parsejs_line_terminator();
      }
    }
    peg$silentFails--;
    if (s2 === peg$FAILED) {
      s1 = void 0;
    } else {
      peg$currPos = s1;
      s1 = peg$FAILED;
    }
    if (s1 !== peg$FAILED) {
      s2 = peg$parsejs_source_character();
      if (s2 !== peg$FAILED) {
        peg$savedPos = s0;
        s1 = peg$c104();
        s0 = s1;
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }
    if (s0 === peg$FAILED) {
      s0 = peg$currPos;
      if (input.charCodeAt(peg$currPos) === 92) {
        s1 = peg$c102;
        peg$currPos++;
      } else {
        s1 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c103); }
      }
      if (s1 !== peg$FAILED) {
        s2 = peg$parsejs_escape_sequence();
        if (s2 !== peg$FAILED) {
          peg$savedPos = s0;
          s1 = peg$c105(s2);
          s0 = s1;
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
      if (s0 === peg$FAILED) {
        s0 = peg$parsejs_line_continuation();
      }
    }

    return s0;
  }

  function peg$parsejs_line_continuation() {
    var s0, s1, s2;

    s0 = peg$currPos;
    if (input.charCodeAt(peg$currPos) === 92) {
      s1 = peg$c102;
      peg$currPos++;
    } else {
      s1 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c103); }
    }
    if (s1 !== peg$FAILED) {
      s2 = peg$parsejs_line_terminator_sequence();
      if (s2 !== peg$FAILED) {
        peg$savedPos = s0;
        s1 = peg$c106();
        s0 = s1;
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }

    return s0;
  }

  function peg$parsejs_escape_sequence() {
    var s0, s1, s2, s3;

    s0 = peg$parsejs_character_escape_sequence();
    if (s0 === peg$FAILED) {
      s0 = peg$currPos;
      if (input.charCodeAt(peg$currPos) === 48) {
        s1 = peg$c107;
        peg$currPos++;
      } else {
        s1 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c108); }
      }
      if (s1 !== peg$FAILED) {
        s2 = peg$currPos;
        peg$silentFails++;
        s3 = peg$parsejs_decimal_digit();
        peg$silentFails--;
        if (s3 === peg$FAILED) {
          s2 = void 0;
        } else {
          peg$currPos = s2;
          s2 = peg$FAILED;
        }
        if (s2 !== peg$FAILED) {
          peg$savedPos = s0;
          s1 = peg$c109();
          s0 = s1;
        } else {
          peg$currPos = s0;
          s0 = peg$FAILED;
        }
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
      if (s0 === peg$FAILED) {
        s0 = peg$parsejs_hex_escape_sequence();
        if (s0 === peg$FAILED) {
          s0 = peg$parsejs_unicode_escape_sequence();
        }
      }
    }

    return s0;
  }

  function peg$parsejs_line_terminator() {
    var s0;

    if (peg$c110.test(input.charAt(peg$currPos))) {
      s0 = input.charAt(peg$currPos);
      peg$currPos++;
    } else {
      s0 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c111); }
    }

    return s0;
  }

  function peg$parsejs_source_character() {
    var s0;

    if (input.length > peg$currPos) {
      s0 = input.charAt(peg$currPos);
      peg$currPos++;
    } else {
      s0 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c112); }
    }

    return s0;
  }

  function peg$parsejs_character_escape_sequence() {
    var s0;

    s0 = peg$parsejs_single_escape_character();
    if (s0 === peg$FAILED) {
      s0 = peg$parsejs_non_escape_character();
    }

    return s0;
  }

  function peg$parsejs_single_escape_character() {
    var s0, s1;

    if (input.charCodeAt(peg$currPos) === 39) {
      s0 = peg$c100;
      peg$currPos++;
    } else {
      s0 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c101); }
    }
    if (s0 === peg$FAILED) {
      if (input.charCodeAt(peg$currPos) === 34) {
        s0 = peg$c97;
        peg$currPos++;
      } else {
        s0 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c98); }
      }
      if (s0 === peg$FAILED) {
        if (input.charCodeAt(peg$currPos) === 92) {
          s0 = peg$c102;
          peg$currPos++;
        } else {
          s0 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c103); }
        }
        if (s0 === peg$FAILED) {
          s0 = peg$currPos;
          if (input.charCodeAt(peg$currPos) === 98) {
            s1 = peg$c113;
            peg$currPos++;
          } else {
            s1 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c114); }
          }
          if (s1 !== peg$FAILED) {
            peg$savedPos = s0;
            s1 = peg$c115();
          }
          s0 = s1;
          if (s0 === peg$FAILED) {
            s0 = peg$currPos;
            if (input.charCodeAt(peg$currPos) === 102) {
              s1 = peg$c116;
              peg$currPos++;
            } else {
              s1 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c117); }
            }
            if (s1 !== peg$FAILED) {
              peg$savedPos = s0;
              s1 = peg$c118();
            }
            s0 = s1;
            if (s0 === peg$FAILED) {
              s0 = peg$currPos;
              if (input.charCodeAt(peg$currPos) === 110) {
                s1 = peg$c119;
                peg$currPos++;
              } else {
                s1 = peg$FAILED;
                if (peg$silentFails === 0) { peg$fail(peg$c120); }
              }
              if (s1 !== peg$FAILED) {
                peg$savedPos = s0;
                s1 = peg$c121();
              }
              s0 = s1;
              if (s0 === peg$FAILED) {
                s0 = peg$currPos;
                if (input.charCodeAt(peg$currPos) === 114) {
                  s1 = peg$c122;
                  peg$currPos++;
                } else {
                  s1 = peg$FAILED;
                  if (peg$silentFails === 0) { peg$fail(peg$c123); }
                }
                if (s1 !== peg$FAILED) {
                  peg$savedPos = s0;
                  s1 = peg$c124();
                }
                s0 = s1;
                if (s0 === peg$FAILED) {
                  s0 = peg$currPos;
                  if (input.charCodeAt(peg$currPos) === 116) {
                    s1 = peg$c125;
                    peg$currPos++;
                  } else {
                    s1 = peg$FAILED;
                    if (peg$silentFails === 0) { peg$fail(peg$c126); }
                  }
                  if (s1 !== peg$FAILED) {
                    peg$savedPos = s0;
                    s1 = peg$c127();
                  }
                  s0 = s1;
                  if (s0 === peg$FAILED) {
                    s0 = peg$currPos;
                    if (input.charCodeAt(peg$currPos) === 118) {
                      s1 = peg$c128;
                      peg$currPos++;
                    } else {
                      s1 = peg$FAILED;
                      if (peg$silentFails === 0) { peg$fail(peg$c129); }
                    }
                    if (s1 !== peg$FAILED) {
                      peg$savedPos = s0;
                      s1 = peg$c130();
                    }
                    s0 = s1;
                  }
                }
              }
            }
          }
        }
      }
    }

    return s0;
  }

  function peg$parsejs_line_terminator_sequence() {
    var s0;

    peg$silentFails++;
    if (input.charCodeAt(peg$currPos) === 10) {
      s0 = peg$c94;
      peg$currPos++;
    } else {
      s0 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c95); }
    }
    if (s0 === peg$FAILED) {
      if (input.substr(peg$currPos, 2) === peg$c132) {
        s0 = peg$c132;
        peg$currPos += 2;
      } else {
        s0 = peg$FAILED;
        if (peg$silentFails === 0) { peg$fail(peg$c133); }
      }
      if (s0 === peg$FAILED) {
        if (input.charCodeAt(peg$currPos) === 13) {
          s0 = peg$c134;
          peg$currPos++;
        } else {
          s0 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c135); }
        }
        if (s0 === peg$FAILED) {
          if (input.charCodeAt(peg$currPos) === 8232) {
            s0 = peg$c136;
            peg$currPos++;
          } else {
            s0 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c137); }
          }
          if (s0 === peg$FAILED) {
            if (input.charCodeAt(peg$currPos) === 8233) {
              s0 = peg$c138;
              peg$currPos++;
            } else {
              s0 = peg$FAILED;
              if (peg$silentFails === 0) { peg$fail(peg$c139); }
            }
          }
        }
      }
    }
    peg$silentFails--;
    if (s0 === peg$FAILED) {
      if (peg$silentFails === 0) { peg$fail(peg$c131); }
    }

    return s0;
  }

  function peg$parsejs_non_escape_character() {
    var s0, s1, s2;

    s0 = peg$currPos;
    s1 = peg$currPos;
    peg$silentFails++;
    s2 = peg$parsejs_escape_character();
    if (s2 === peg$FAILED) {
      s2 = peg$parsejs_line_terminator();
    }
    peg$silentFails--;
    if (s2 === peg$FAILED) {
      s1 = void 0;
    } else {
      peg$currPos = s1;
      s1 = peg$FAILED;
    }
    if (s1 !== peg$FAILED) {
      s2 = peg$parsejs_source_character();
      if (s2 !== peg$FAILED) {
        peg$savedPos = s0;
        s1 = peg$c104();
        s0 = s1;
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }

    return s0;
  }

  function peg$parsejs_escape_character() {
    var s0;

    s0 = peg$parsejs_single_escape_character();
    if (s0 === peg$FAILED) {
      s0 = peg$parsejs_decimal_digit();
      if (s0 === peg$FAILED) {
        if (input.charCodeAt(peg$currPos) === 120) {
          s0 = peg$c140;
          peg$currPos++;
        } else {
          s0 = peg$FAILED;
          if (peg$silentFails === 0) { peg$fail(peg$c141); }
        }
        if (s0 === peg$FAILED) {
          if (input.charCodeAt(peg$currPos) === 117) {
            s0 = peg$c142;
            peg$currPos++;
          } else {
            s0 = peg$FAILED;
            if (peg$silentFails === 0) { peg$fail(peg$c143); }
          }
        }
      }
    }

    return s0;
  }

  function peg$parsejs_decimal_digit() {
    var s0;

    if (peg$c82.test(input.charAt(peg$currPos))) {
      s0 = input.charAt(peg$currPos);
      peg$currPos++;
    } else {
      s0 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c83); }
    }

    return s0;
  }

  function peg$parsejs_hex_escape_sequence() {
    var s0, s1, s2, s3, s4, s5;

    s0 = peg$currPos;
    if (input.charCodeAt(peg$currPos) === 120) {
      s1 = peg$c140;
      peg$currPos++;
    } else {
      s1 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c141); }
    }
    if (s1 !== peg$FAILED) {
      s2 = peg$currPos;
      s3 = peg$currPos;
      s4 = peg$parsejs_hex_digit();
      if (s4 !== peg$FAILED) {
        s5 = peg$parsejs_hex_digit();
        if (s5 !== peg$FAILED) {
          s4 = [s4, s5];
          s3 = s4;
        } else {
          peg$currPos = s3;
          s3 = peg$FAILED;
        }
      } else {
        peg$currPos = s3;
        s3 = peg$FAILED;
      }
      if (s3 !== peg$FAILED) {
        s2 = input.substring(s2, peg$currPos);
      } else {
        s2 = s3;
      }
      if (s2 !== peg$FAILED) {
        peg$savedPos = s0;
        s1 = peg$c144(s2);
        s0 = s1;
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }

    return s0;
  }

  function peg$parsejs_hex_digit() {
    var s0;

    if (peg$c145.test(input.charAt(peg$currPos))) {
      s0 = input.charAt(peg$currPos);
      peg$currPos++;
    } else {
      s0 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c146); }
    }

    return s0;
  }

  function peg$parsejs_unicode_escape_sequence() {
    var s0, s1, s2, s3, s4, s5, s6, s7;

    s0 = peg$currPos;
    if (input.charCodeAt(peg$currPos) === 117) {
      s1 = peg$c142;
      peg$currPos++;
    } else {
      s1 = peg$FAILED;
      if (peg$silentFails === 0) { peg$fail(peg$c143); }
    }
    if (s1 !== peg$FAILED) {
      s2 = peg$currPos;
      s3 = peg$currPos;
      s4 = peg$parsejs_hex_digit();
      if (s4 !== peg$FAILED) {
        s5 = peg$parsejs_hex_digit();
        if (s5 !== peg$FAILED) {
          s6 = peg$parsejs_hex_digit();
          if (s6 !== peg$FAILED) {
            s7 = peg$parsejs_hex_digit();
            if (s7 !== peg$FAILED) {
              s4 = [s4, s5, s6, s7];
              s3 = s4;
            } else {
              peg$currPos = s3;
              s3 = peg$FAILED;
            }
          } else {
            peg$currPos = s3;
            s3 = peg$FAILED;
          }
        } else {
          peg$currPos = s3;
          s3 = peg$FAILED;
        }
      } else {
        peg$currPos = s3;
        s3 = peg$FAILED;
      }
      if (s3 !== peg$FAILED) {
        s2 = input.substring(s2, peg$currPos);
      } else {
        s2 = s3;
      }
      if (s2 !== peg$FAILED) {
        peg$savedPos = s0;
        s1 = peg$c144(s2);
        s0 = s1;
      } else {
        peg$currPos = s0;
        s0 = peg$FAILED;
      }
    } else {
      peg$currPos = s0;
      s0 = peg$FAILED;
    }

    return s0;
  }


    let flatten = (head, tail, idx) => {
      let res = [head];
      tail.forEach((el) => { 
        if (el && el[idx])
          res.push(el[idx]);
      });
      return res;

    };

    let flatstr = (x, rejectSpace, joinChar) => {
      if (joinChar == null) {
        joinChar = '';
      }
      return R$1.reject(R$1.isEmpty, R$1.flatten(x)).join(joinChar);
    };



  peg$result = peg$startRuleFunction();

  if (peg$result !== peg$FAILED && peg$currPos === input.length) {
    return peg$result;
  } else {
    if (peg$result !== peg$FAILED && peg$currPos < input.length) {
      peg$fail(peg$endExpectation());
    }

    throw peg$buildStructuredError(
      peg$maxFailExpected,
      peg$maxFailPos < input.length ? input.charAt(peg$maxFailPos) : null,
      peg$maxFailPos < input.length
        ? peg$computeLocation(peg$maxFailPos, peg$maxFailPos + 1)
        : peg$computeLocation(peg$maxFailPos, peg$maxFailPos)
    );
  }
}

let parse = peg$parse;

const squel = squelbase.useFlavour('postgres');


const toSql = R$1.invoker(0, "toSql");
const clone = R$1.invoker(0, "clone");
const getAttrs = R$1.pluck('attr');

let aliasid = 0;
let newAlias = (prefix="tmp") => `${prefix}_${aliasid++}`;


/*
 * attr: attribute string
 * bound: [min, max]
 * n: number of samples
 */
let Samples = (({attr, bound, n}) => {
  let me = () => {};
  me.classType = "Samples";
  me.bound = bound;
  me.attr = attr;
  me.min = bound[0];
  me.max = bound[1];
  me.n = n;

  me.toSql = () => {
    let q = squel.select()
      .from(`generate_series(1, ${me.n})`)
      .field(`generate_series * ${(me.max-me.min)/me.n} + ${me.min}`, me.attr);
    return q;
  };

  me.inferType = (alias) => {
    if (alias == me.attr) return alias
    return null;
  };
  me.traverse = (f) => f(me);
  me.clone = () => Sample({ attr:me.attr, bound: [me.min, me.max], n:me.n });
  me.schema = () => [Attr(me.attr)];
  return me;
});


/*
 * Af: list of Attr
 * Ac: list of Attr.  default: []
 * y:  Attr  default: Attr("y")
 * model: linear, logistic, poly, or glm
 */
let Model = (({child, Af, Ac, y, model}) => {
  let me = () => {};
  me.classType = "Model";
  me.Af = Af;
  me.Ac = Ac || [];
  me.y = y || Attr("y");
  me.c = child;
  me.model = model || "linear";
  me.modelTableName = newAlias('modelout');
  me.input = newAlias("modelin"); // used to refer to child subq
  me.bounds = [];
  me.n = 50;

  me.setBounds = (bounds) => { 
    if (bounds.length < me.Af.length) {
      console.error("bounds: ", bounds);
      console.error("Af: ", R$1.pluck("attr", me.Af));
      throw new Error("Missing bounds for features")
    }
    me.bounds = bounds; 
    let perdim = Math.pow(500, 1/R$1.keys(bounds).length);
    me.n = Math.max(3, Math.round(Math.min(perdim, me.n)));
  };

  me.setup = async (db) => {
    // http://madlib.apache.org/docs/latest/group__grp__linreg.html
    let subq = me.c.toSql();
    let createQs = [
      `DROP TABLE IF EXISTS ${me.input};`,
      `DROP TABLE IF EXISTS ${me.modelTableName};`,
      `DROP TABLE IF EXISTS ${me.modelTableName}_summary;`,
      `CREATE TABLE ${me.input} as ${subq.toString()};`
    ];

    console.group("Model.setup");
    for (const q of createQs) {
      console.info(q);
      await runQuery(db, q);
    }

    let list = R$1.concat([1], getAttrs(me.Af));
    let features = `ARRAY[${list.join(',')}]`;
    let grouping = (me.Ac.length)? `'${getAttrs(me.Ac).join(',')}'`: 'null';
    let select = "";

    if (me.model == "linear") {
       select = `madlib.linregr_train(
        '${me.input}', 
        '${me.modelTableName}', 
        '${me.y.attr}',
        '${features}',
        ${grouping}
      )`;
    } else if (me.model == "logistic") {
      select = `madlib.logregr_train(
        '${me.input}',
        '${me.modelTableName}',
        '${me.y.attr}',
        '${features}',
        ${grouping}
      )`;
    } else if (me.model == "glm") {
      select = `madlib.glm(
        '${me.input}',
        '${me.modelTableName}',
        '${me.y.attr}',
        '${features}',
        'family=gaussian,link=log',
        ${grouping}
      ) `;
    }
    let q = squel.select().field(select);
    console.info(q.toString());
    console.groupEnd();
    let res = await runQuery(db, q.toString());

    return me;
  };

  // returns a query that, given bounds, will run the predictions
  me.toSql = () => {
    let q = squel.select();

    let featureRefs = [1];
    me.bounds.forEach(([A, bound]) => {
      let attr = A.attr;
      let samples = Samples({attr, bound, n:me.n});
      let samAlias = newAlias("samples");
      q.from(samples.toSql(), samAlias);
      q.field(`${samAlias}.${attr}`, attr);
      featureRefs.push(`${samAlias}.${attr}`);
    });
    let features = `ARRAY[${featureRefs.join(',')}]`;

    let predict = `madlib.linregr_predict(
      ${me.modelTableName}.coef, 
      ${features})`;
    if (me.model == "logistic") 
      predict = `madlib.logregr_predict(
        ${me.modelTableName}.coef, 
        ${features})`;
    else if (me.model == "glm")
      predict = `madlib.glm_predict(
        ${me.modelTableName}.coef, 
        ${features}, 'log')`;

    q.from(me.modelTableName);
    q.field(predict, me.y.attr);
    me.Ac.forEach((a) => {
      q.field(`${me.modelTableName}.${a.attr}`, a.attr);
    });
    return q
  };

  me.traverse = (f) => {
    if (f(me) == false) return;
    me.c.traverse(f);
  };
  me.clone = () => Model({
    child: me.c.clone(),
    Af: me.Af.map(clone),
    Ac: me.Ac.map(clone),
    y: me.y.clone()
  });
  me.schema = () => R$1.flatten([me.Af, me.Ac, me.y]);
  me.inferType = (alias) => me.c.inferType(alias);

  return me;
});


let Union = (({children}) => {
  let me = () => {};
  me.classType = "Union";
  me.cs = children;
  me.alias = newAlias("union");

  me.toSql = () => {
    let subq = R$1.reduce((acc, c) => acc.union(c.toSql()), 
      me.cs[0].toSql(),
      R$1.tail(me.cs));
    return squel.select().from(subq, me.alias)
  };

  me.traverse = (f) => {
    if (f(me) == false) return;
    me.cs.forEach((c) => c.traverse(f));
  };

  me.clone = () => {
    return Union({children: me.cs.map(clone)})
  };
  me.schema = () =>  me.cs[0].schema(); 
  me.inferType = (alias) => me.cs[0].inferType(alias);

  return me;
});

let Where = (({exprs, child}) => {
  let me = () => {};
  me.classType = "Where";
  me.exprs = R$1.is(Array, exprs)? exprs : [exprs];
  me.c = child;

  me.toSql = () => {
    var q = me.c.toSql();
    me.exprs.forEach((e) => q.where(e.toSql()));
    return q;
  };

  me.traverse = (f) => {
    if (f(me) == false) return;
    me.exprs.forEach((e) => e.traverse(f));
    me.c.traverse(f);
  };


  me.addWherePredicate = (e) => {
    me.exprs.push(e);
    return me;
  };

  me.clone = () => {
    return Where({
      exprs: me.exprs.map(clone),
      child: clone(me.c)
    });
  };
  me.schema = () =>  me.c.schema();
  me.inferType = (alias) => me.c.inferType(alias);

  return me;
});

/*
 * type: left, right, full.  else: inner
 * l,r: Query Plans
 * on: [Expr, ...]
 */
let Join = (({type, l, r, on, lalias, ralias}) => {
  let me = () => {};
  me.classType = "Join";
  me.type = type || "inner";
  me.l = l;
  me.r = r;
  me.on = on; // list of Expr

  me.lalias = lalias;
  me.ralias = ralias;
  if (!me.lalias || !me.ralias) {
    throw new Error("Join inputs must have aliases: ", me.lalias, me.ralias);
  }

  me.traverse = (f) => {
    if (f(me) == false) return;
    me.on.forEach((e) => e.traverse(f));
    me.l.traverse(f);
    me.r.traverse(f);
  };

  me.toSql = () => {
    let l = me.l.toSql();
    let r = me.r.toSql(); 
    var q = squel.select().from(l, me.lalias);
    let f = (accum, e) => accum.and(e.toSql());
    let joinCondition = squel.expr().and("1=1");

    if (me.on && me.on.length)
      joinCondition = R$1.reduce(f, squel.expr(), me.on);

    if (me.type == "left")
      q.left_join(r, ralias, joinCondition);
    else if (me.type == "right")
      q.right_join(r, ralias, joinCondition);
    else if (me.type == "full")
      q.outer_join(r, ralias, joinCondition);
    else
      q.join(r, ralias, joinCondition);
    
    return q;
  };

  me.clone = () => {
    return Join({
      type: me.type,
      l: clone(me.l) ,
      r: clone(me.r),
      lalias: me.lalias,
      ralias: me.ralias,
      on: me.on.map(clone)
    });
  };
  me.schema = () => {
    let schema = [];
    R$1.concat(me.l.schema(), me.r.schema()).map((attr) => {
      attr = attr.clone();
      attr.table = null;
      schema.push(attr);
    });
    return schema;
  };
  me.inferType = (alias) => {
    let laliases = getAttrs(me.l.schema());
    let raliases = getAttrs(me.r.schema());
    let ltype = null, rtype = null;
    if (R$1.contains(alias, laliases))
      ltype = me.l.inferType(alias);
    if (R$1.contains(alias, raliases))
      rtype = me.r.inferType(alias);
    let types = R$1.uniq(R$1.reject(R$1.isNil, [ltype, rtype]));
    if (types.length)
      return types.join(",")
    return null;
  };

  return me;
});


/*
 * Convention: query is left, model is right
 * 
 */
let ModelQueryJoin = ({l, r, lalias, ralias}) => {
  let me = () => {};
  me.classType = "ModelJoin";
  me.l = l;
  me.r = r;
  me.lalias = lalias;
  me.ralias = ralias;

  if (r.classType != "Model") 
    throw new Error("ModelQueryJoin expects Model as right side")


  me.toSql = () => {
    let q = squel.select();
    let lattrs = R$1.pluck("attr", me.l.schema());
    let list = [1];

    me.r.bounds.forEach(([A, bound]) => {
      if (R$1.contains(A.attr, lattrs)) {
        q.field(`${me.lalias}.${A.attr}`, A.attr);
        list.push(`${me.lalias}.${A.attr}`);
        return;
      }
      let attr = A.attr;
      let samples = Samples({attr, bound, n: me.r.n});
      let samAlias = newAlias("samples");
      q.from(samples.toSql(), samAlias);
      q.field(`${samAlias}.${attr}`, attr);
      list.push(`${samAlias}.${attr}`);
    });

    let features = `ARRAY[${list.join(',')}]`;
    let predict = `madlib.linregr_predict(
      ${me.ralias}.coef, 
      ${features})`;
    if (me.r.model == "logistic") 
      predict = `madlib.logregr_predict(
        ${me.ralias}.coef, 
        ${features})`;
    else if (me.r.model == "glm")
      predict = `madlib.glm_predict(
        ${me.ralias}.coef, 
        ${features}, 'log')`;
    q.field(predict, r.y.attr);

    let joinCond = squel.expr().and("1=1");
    if (me.r.Ac && me.r.Ac.length) {
      me.r.Ac.forEach((a) => {
        q.field(`${me.ralias}.${a.attr}`);
        if (!R$1.contains(a.attr, R$1.pluck("attr", me.l.schema()))) return
        joinCond.and(`${me.lalias}.${a.attr} = ${me.ralias}.${a.attr}`);
      });
    } 

    q.from(me.r.modelTableName, me.ralias)
      .join(me.l.toSql(), me.lalias, joinCond);

    me.r.Ac.forEach((a) => q.field(`${me.ralias}.${a.attr}`));
    //me.r.Af.forEach((a) => q.field(`${me.lalias}.${a.attr}`))
      
    return q;
  };

  me.traverse = (f) => {
    if (f(me) == false) return;
    me.l.traverse(f);
    me.r.traverse(f);
  };

  me.clone = () => ModelQueryJoin({
    l: me.l.clone(),
    r: me.r.clone(),
    lalias: me.lalias,
    ralias: me.ralias
  });

  me.schema = () => me.l.schema();
  me.inferType = (alias) => me.l.inferType(alias);

  return me;
};


let Source = (({source, schema, alias}) => {
  let me = () => {};
  me.classType = "Source";
  me.source = source;  // either  str table name or root operator of subquery
  me._schema = schema;  
  me.alias = alias;
  me.isBaseTable = R$1.is(String, me.source);

  me.toSql = () => {
    if (me.isBaseTable) return squel.select().from(me.source, me.alias)
    return squel.select().from(me.source.toSql(), me.alias)
  };

  me.traverse = (f) => {
    if (f(me) == false) return;
    if (!me.isBaseTable) me.source.traverse(f);
  };


  me.clone = () => {
    return Source({
      source: me.isBaseTable? me.source : clone(me.source),
      schema: me._schema? me._schema.map(clone) : null,
      alias: me.alias
    })
  };
  me.schema = (newSchema) => {
    if (newSchema && me.isBaseTable)
      me._schema = newSchema;
    if (me.isBaseTable) 
      return me._schema;
    return me.source.schema()
  };
  me.inferType = (alias) => {
    if (me.isBaseTable) return alias
    return me.source.inferType(alias)
  };

  return me;
});

let Project = (({exprs, child}) => {
  let me = () => {};
  me.classType = "Project";
  me.pcs = exprs; // PClause objects
  me.c = child;

  me.toSql = () => {
    var q = me.c? me.c.toSql() : squel.select();
    me.pcs.forEach((pc) => q.field(pc.toSql(), pc.alias));
    return q
  };

  me.traverse = (f) => {
    if (f(me) == false) return;
    me.pcs.forEach((pc) => pc.traverse(f));
    if (me.c)
      me.c.traverse(f);
  };


  me.clone = () => {
    return Project({
      exprs: me.pcs.map(clone),
      child: me.c? me.c.clone(): null
    })
  };

  me.schema = () => {
    let schema = [];
    me.pcs.forEach((pc) => {
      if (pc.e.classType == "Star") {
        schema = R$1.concat(schema, me.c.schema());
      } else {
        schema.push(Attr({ attr: pc.alias, type: pc.getType() }));
      }
    });
    return schema
  };

  me.inferType = (alias) => {
    let type = null;
    let hasStar = false;
    me.pcs.forEach((pc) => {
      if (pc.alias == alias) {
        if (!me.c) {
          type = pc.inferType();
        } else {
          let attrs = [];
          pc.traverse((op) => {
            if (op.classType == "Attr")
              attrs.push(op.attr);
          });
          let types = R$1.uniq(attrs)
            .map((refAlias) => me.c.inferType(refAlias));
          type = R$1.uniq(types).join(",");
        }
      }
      if (pc.e.classType == "Star")
        hasStar = true;
    });

    if (!type && me.c && hasStar)
      type = me.c.inferType(alias);

    return type;
  };

  return me;
});

let GroupBy = (({Agb, Fs, child}) => {
  let me = () => {};
  me.classType = "GroupBy";
  me.Agb = Agb || [];  // grouping expressions: list of PClauses
  me.Fs = Fs || [];    // agg functions: list of PClauses
  me.c = child;

  // XXX: we assume that the expressions are all attribute references!!!
  if (R$1.any((pc) => pc.e.classType != "Attr", me.Agb)) {
    console.log(me.Agb.map((pc)  => pc.toSql().toString()));
    console.error(me.Agb.map((pc) => pc.e.classType));
    throw new Error("Grouping expressions must all be Attributes:", me.Agb)
  }


  me.toSql = () => {
    let q = me.c.toSql();
    R$1.concat(me.Agb, me.Fs).forEach((pc) => 
      q.field(pc.e.toSql(), pc.alias)
    );
    me.Agb.forEach((g) => {
      if (g.e.classType != "Value")
        q.group(g.e.toSql());
    });
    return q
  };

  me.traverse = (f) => {
    if (f(me) == false) return;
    R$1.concat(me.Agb, me.Fs).forEach((e) => e.traverse(f));
    me.c.traverse(f);
  };


  me.terms = () => R$1.reject(R$1.isNil, R$1.concat(me.Agb, me.Fs));

  me.clone = () => {
    return GroupBy({ 
      Agb: me.Agb.map(clone),
      Fs: me.Fs.map(clone),
      child: me.c.clone()
    })
  };

  me.schema = () => {
    return R$1.concat(me.Agb, me.Fs).map((pc) => {
      return Attr({ attr: pc.alias, type: pc.getType() })
    })
  };

  me.inferType = (alias) => {
    let type = null;
    R$1.concat(me.Agb, me.Fs).forEach((pc) => {
      if (pc.alias == alias)
        type = pc.inferType();
    });
    return type;
  };

  return me;
});


const aggfnames = [
  "avg",
  "mean",
  "min",
  "max",
  "std",
  "count"
];

// Helper function for parser to use
GroupBy.termsToAgbFs = (terms) => {
  let aliases = {};
  let ret = {
    Agb: [], Fs: []
  };
  let containsAggFunc = (pc) => {
    let contains = false;
    pc.traverse((op) => {
      if (op.classType == "Func" && R$1.contains(op.fname, aggfnames)) {
        contains = true;
        return false;
      }
    });
    return contains;
  };
  terms.forEach((pc) => {
    if (aliases[pc.alias]) 
      throw Error(`Duplicate aliases: ${terms}`)
    aliases[pc.alias] = true;

    if (containsAggFunc(pc))
      ret.Fs.push(pc);
    else
      ret.Agb.push(pc);
  });
  return ret;
};

let PClause = (({e, alias}) => {
  let me = () => {};
  me.classType = "PClause";
  me.e = e;
  me.alias = alias || null;

  if (alias && !R$1.is(String, alias)) 
    throw new Error("PClause alias should be string: ", alias)

  me.getType = () => me.e.getType();

  me.toSql = () => e.toSql();

  me.traverse = (f) => {
    if (f(me) == false) return;
    me.e.traverse(f);
  };

  me.clone = () => {
    return PClause({ e:e.clone(), alias })
  };

  me.inferType = () => me.e.inferType();

  return me;
});














/*
 * op: operation string 
 * l, r: Expr objects
 *
 * TODO: wrap with CASE to handle nulls for l or r
 */
let Expr = (({op, l, r}) => {
  let me = () => {};
  me.classType = "Expr";
  me.op = op;
  me.l = l;
  me.r = r;

  me.getType = () => { return "Number"; };
  me.inferType = () => {
    let ltype = me.l.inferType();
    if (!me.r) return ltype;
    let rtype = me.r.inferType();
    if (ltype == rtype) return ltype;
    return `${ltype},${rtype}`
  };

  me.toSql = () => {
    if (R$1.isNil(r)) 
      return `${op}${l.toSql()}`
    return `${l.toSql()} ${op} ${r.toSql()}`
  };

  me.traverse = (f) => {
    if (f(me) == false) return;
    l.traverse(f);
    if (r) r.traverse(f);
  };


  me.clone = () => {
    return Expr({
      op, 
      l:l.clone(), 
      r:(r?r.clone():null)
    })
  };
  return me;
});

let Paren = (({expr}) => {
  let me = () => {};
  me.classType = "Paren";
  me.e = expr;

  me.getType = () => me.e.getType();
  me.inferType = () => me.e.inferType();
  me.toSql = () => `(${me.e.toSql()})`;
  me.traverse = (f) => {
    if (f(me) != false) me.e.traverse(f);
  };
  me.clone = () => Paren({expr: me.e.clone()});
  return me;
});

/*
 * type: "Literal", "Number"
 */
let Value = (({type, value, raw}) => {
  let me = () => {};
  me.classType = "Value";
  me.value = value;
  me.type = type || (R$1.is(Number, value)? "Number" : "Literal");
  me.raw = (raw===undefined)? false : raw;

  me.getType = () => { return me.type; };
  me.inferType = () => me.type;

  me.toSql = () => {
    if (me.type == "Literal" && !me.raw) return `'${value}'`
    return String(value)
  };

  me.traverse = (f) => {
    f(me);
  };

  me.clone = () => {
    return Value({type: me.type, value: me.value, raw: me.raw})
  };
  return me;
});

let Star = (() => {
  let me = () => {};
  me.classType = "Star";

  me.getType = () => null;
  me.inferType = () => {
    throw new Error("Star.inferType not defined")
  };
  me.clone = () => Star();
  me.toSql = () => '*';
  me.traverse = (f) => f(me);

  return me;
});

/*
 * opts: { 
 *  table // string
 *  attr  // str
 *  type: // Literal or Number
 * }
 */
let Attr = ((opts) => {
  let me = () => {};
  me.classType = "Attr";

  if (R$1.is(String, opts)) {
    opts = { attr: opts };
  }

  me.table = opts.table;
  me.attr = opts.attr;
  me.type = opts.type || "Literal";

  me.getType = () => { return me.type; };
  me.inferType = () => me.attr;

  me.toSql = () => {
    if (R$1.isNil(me.table)) return me.attr;
    return `${me.table}.${me.attr}`;
  };

  me.traverse = (f) => f(me);


  me.clone = () => {
    return Attr({table:me.table, attr:me.attr})
  };
  return me;
});

/*
 * fname: string of SQL function name
 * args: Array of Expr objects
 * distinct: boolean.  fname( distinct args)
 */
let Func = (({fname, args, distinct}) => {
  let me = () => {};
  me.classType = "Func";
  me.fname = fname;
  me.args = R$1.is(Array, args)? args : [args];
 me.args = R$1.reject(R$1.isNil, me.args);
  me.distinct = distinct || false;

  me.getType = () => { return "Number" };
  me.inferType = () => {
    let argTypes = R$1.uniq(me.args.map((e) => e.inferType()));
    if (R$1.contains(R$1.toLower(me.fname), ["avg", "min", "max", "std"])) {
      return argTypes.join(",")
    }
    if (me.fname == "ifnull")
      return argTypes[0];
    return `${me.fname}<${argTypes.join(",")}>`;
  };

  me.toSql = () => {
    const argsStr = me.args.map(toSql()).join(", ");
    return `${me.fname}(${me.distinct? 'distinct' : ''} ${argsStr})`
  };

  me.traverse = (f) => {
    if (f(me) == false) return;
    me.args.forEach((e) => e.traverse(f));
  };


  me.clone = () => {
    return Func({fname:fname, args:me.args.map(clone), distinct:distinct})
  };
  return me;
});

var query = /*#__PURE__*/Object.freeze({
__proto__: null,
Samples: Samples,
Model: Model,
Union: Union,
Where: Where,
Join: Join,
ModelQueryJoin: ModelQueryJoin,
Source: Source,
Project: Project,
GroupBy: GroupBy,
PClause: PClause,
Expr: Expr,
Paren: Paren,
Value: Value,
Star: Star,
Attr: Attr,
Func: Func
});

const squel$1 = squelbase.useFlavour('postgres');

let debug = ((msg) => {
  try {
    var el = $("#text");
    var c = document.createElement("div");
    c.innerText = msg;
    c.className = "alert alert-warning";
    el.prepend(c);
  } catch (e) {
  }
  console.log(msg);
});


let makeXhrRequest = async (url) => {
  return new Promise((resolve, reject) => {
    var xhr = new XMLHttpRequest();
    xhr.open('GET', url, true);
    xhr.responseType = 'arraybuffer';

    xhr.onload = function(e) {
      resolve(this.response);
    };
    xhr.onerror = () => reject({ 
      status: xhr.status, 
      statusText: xhr.statusText
    });
    xhr.send();
  });
};

let RemoteDB = (({url}) => {
  let me = () => {};

  me.exec = async (q) => {
    const result = await $.ajax({
      url: url || "http://localhost:8000/query",
      type: "GET",
      data: { q },
      dataType: "json"
    });
    return result;
  };
  me.getSchemasQuery = "select tablename as tbl_name from pg_tables where position('tmp' in tablename) = 0 and position('model' in tablename) = 0 and schemaname = 'public';";

  return me;
});

let loadSqliteDB = async (SQL, url) => {
  const response = await makeXhrRequest(url);
  var uInt8Array = new Uint8Array(response);
  let db = new SQL.Database(uInt8Array);
  db.getSchemasQuery = "select tbl_name from sqlite_master where type='table'";
  return db;
};

let runQuery = async (db, q) => {
  try {
    let [data] = await db.exec(q);
    data = data.values.map((vals) => {
      return Object.fromEntries( vals.map((v,i) => [data.columns[i], v]));
    });
    return data;
  } catch (e) {
    console.error(q);
    console.log(e);
    throw e;

  }
};


// given known facetting attribute, determine the "buckets" and define 
// filter query for each bucket
//
// @table: String table/view name
// @facet: String attribute name used for faceting
//         TODO: support Attr or Expr objects for @facet
let getFacetBuckets = async (db, q, facet) => {
  // TODO: better facet buckets.  currently uses every distinct value
  //       1. if numeric, compute counts and determine equidepth buckets
  //       2. if string, current approach is fine
  let fq = squel$1.select()
    .from(q.toSql(), 'facettable')
    .field(`distinct ${facet}`, "val")
    .order(facet);
  let rows = await runQuery(db, fq.toString());
  let specs = rows.map(({val}) => {
    let spec = {                       // facet = val
      where: Expr({
        op:"=", l: Attr(facet), 
        r: Value({type:"Literal", value: val})
      }),
      facet,
      val
    };
    return spec;
  });
  return specs;
};


//
// @el: jQuery element
// @css: key-val object of css attributes to set
//
function setAndSaveCss(el, css) {
  R$1.forEach(([k,v]) => {
    el.attr(k, el.attr(k) || el.css(k));
  }, R$1.toPairs(css));
  el.css(css);
}

function restoreCss(el, cssAttrs) {
  cssAttrs.forEach((k) => {
    el.css(k, el.attr(k) || '');
    el.removeAttr(k);
  });
}


function descendantOfClass(n, klass) {
	while(n.parentNode) {
	  if ($(n).hasClass(klass)) return true;
	  n = n.parentNode;
	}
	return false;
  }


/*
 * inner join input bounds on Attr, and unions their min/max
 *
 * bounds: [ [Attr, [min, max], ... ]
 */
function mergeBounds(bounds1, bounds2) {
  let output = [];
  bounds1.forEach(([attr1, [min1, max1]]) => {
    bounds2.forEach(([attr2, [min2, max2]]) => {
      if (attr1.attr != attr2.attr) return;
      output.push(
        [
          attr1.clone(), 
          [Math.min(min1,min2), Math.max(max1,max2)]
        ]
      );
    });
  });
  return output;
}

function bboxOverlap(b1, b2) {
  return !(
    b1.l + b1.w < b2.l ||
    b2.l + b2.w < b1.l ||
    b1.t + b1.h < b2.t ||
    b2.t + b2.h < b1.t
  )
}

const squel$2 = squelbase.useFlavour('postgres');


const toSql$1 = R$1.invoker(0, "toSql");
const clone$1 = R$1.invoker(0, "clone");



let VCA = (({app}) => {
  let me = () => {};
  me.app = app;
  me.db = app.db;

  var id = 0;

  let newAlias = (prefix="t") => `${prefix}${id++}`;


  // Naive schema matcher 
  // Returns null and complains if match is ambiguous
  // Wrapper functions can check for incomplenteness
  me.getMatch = (v1, v2) => {
    let laliases = VCA.getAliases(v1.q);
    let raliases = VCA.getAliases(v2.q);
    let ltypes = laliases.map(v1.q.inferType);
    let rtypes = raliases.map(v2.q.inferType);
    let match = {};  // left alias -> right alias
    let rmatch = {}; // the reverse: right -> left


    let isMeasure = (v,alias) => v.mapping.measure == alias;
    let checkMatch = (lalias, ralias) => {
      if (match[lalias] || rmatch[ralias])  {
        console.error(`${lalias}->${ralias} but already has match:`, match);
        return false
      }
      return true;
    };

    console.group("getMatch");
    let findBestMatch = (lalias, ltype) => {
      let candidates = [];
      for (let [ralias, rtype] of R$1.zip(raliases, rtypes)) {
        console.log("findbestmatch", lalias, ltype, ralias, rtype);
        if (isMeasure(v1,lalias) && isMeasure(v2, ralias)) {
          console.log("both are measures");
          if (ltype == rtype || ltype == "Number" || rtype == "Number") {
            candidates.push({ ralias, rtype });
            continue
          }
        } else if (isMeasure(v1,lalias) || isMeasure(v2, ralias)) 
          continue

        if (ltype == rtype) 
          candidates.push({ ralias, rtype });
      }

      R$1.sortBy(({ralias, rtype}) => {
        return -((ralias==lalias)*100 + (ltype == rtype)*1);
      }, candidates);
      return (candidates.length)? candidates[0].ralias : null;
    };
    console.groupEnd();

    
    for (let [lalias, ltype] of R$1.zip(laliases, ltypes)) {
      let ralias = findBestMatch(lalias, ltype);
      if (!ralias) continue;
      if (checkMatch(lalias, ralias)) {
        match[lalias] = ralias;
        rmatch[ralias] = lalias;
      } else 
        return null;
    }
    return match;
  };

  //
  // returns: v1alias -> v2alias
  //          mapping from v1.q's schema to v2.q's schema
  me.getBinaryDotMatch = (v1, v2) => {
    // TODO: matces should be based on data attributes actually mapped
    // to visual variables!
    let match = me.getMatch(v1, v2);
    let rmatch = R$1.invertObj(match);

    let laliases = VCA.getAliases(v1.q);
    let raliases = VCA.getAliases(v2.q);
    let lmeasures = laliases.filter((la) => v1.mapping.measure == la);
    let rmeasures = raliases.filter((ra) => v2.mapping.measure == ra);

    // All v2.Agbs should have matches to support non-exact schema composition
    let rAgbs = VCA.getAgb(v2.q);
    if(!R$1.all((pc)=>rmatch[pc.alias], rAgbs)) {
      console.error("Not all v2.Agbs have matches", 
        R$1.pluck("alias", VCA.getAgb(v1.q)),
        R$1.pluck("alias", rAgbs), 
        "match:", rmatch);
      return null;
    }

    // In general, if query-model join, then schema should fully match.
    //let isModel = (v)=> v.q.classType == "Model"
    //if (isModel(v1) && !isModel(v2)) {
    //  let lAgbs = VCA.getAgb(v1.q)
    //  if (!R.all((pc)=>match[pc.alias], lAgbs)) {
    //    console.error("Model○Query: not all v1.Agbs have matches",
    //      R.pluck("alias", lAgbs),
    //      R.pluck("alias", rAgbs),
    //      "match:", match)
    //    return null;
    //  }
    //}

    // Measures should be matched
    if (!R$1.all((alias) => match[alias], lmeasures)) { 
      console.error("v1 measure not matched: ", 
        lmeasures, "match:", match);
      return null;
    }
    if (!R$1.all((alias) => rmatch[alias], rmeasures)) {
      console.error("v2 measure not matched: ", rmeasures, rmatch); 
      return null;
    }
    return match;
  };

  me.getNaryDotMatch = (vs) => {
    const isCanonical = (q) => {
      let ops = VCA.find(q, ["Join", "ModelQueryJoin", "ModelModelJoin", "GroupBy"]);
      let b =  !ops.length || ops[0].classType == "GroupBy";
      if (!b)
        console.error("NaryDot: view not in canonical form", q);
      return b;
    };
    if (!R$1.all(isCanonical, R$1.pluck("q", vs))) return null;
    if (vs.length <= 1) return {}

    let v1 = vs[0];
    let matches = R$1.tail(vs).map((v2) => me.getBinaryDotMatch(v1, v2));
    // check matches are all the same
    if (R$1.all(R$1.equals(matches[0]), R$1.tail(matches)))
      return matches[0]
    return null;
  };

  me.getUnionMatch = (vs) => {
    let schemas = vs.map((v) => R$1.pluck("attr", v.q.schema()));
    return R$1.all(R$1.equals(schemas[0]), R$1.tail(schemas))
  };


  // Given a new data attribute and current visual mapping,
  // update the mapping
  //
  // TODO: remove hard coded rule (use Draco or something)
  me.assignVisualMapping = (schema, mapping) => {
    let dattrs = R$1.pluck("attr", schema);
    let newDattrs = R$1.difference(dattrs, R$1.values(mapping));

    let vattrs = ['x', 'y', 'color', 'shape', 'column', 'size' ]; 
    let newMapping = { mark: "bar" };
    R$1.forEachObjIndexed((dattr, vattr) => {
      if (R$1.contains(vattr, ["meoasure", "mark"]) || R$1.contains(dattr, dattrs))
        newMapping[vattr] = dattr;
    }, mapping);
    
    if (newMapping.mark == "table") {
      newDattrs.forEach((dattr) => newMapping[dattr] = dattr);
      return newMapping;
    } 

    if (newMapping.mark == "bar" && newDattrs.length == 1) { 
      newMapping['x'] = newDattrs[0];
      newMapping['color'] = newDattrs[0];
      newMapping['column'] = mapping['x'];
      return newMapping;
    } 

    // if there are missing positional attributes but mapped nonpositional attributes
    // then swap
    let isMapped = (vattr) => R$1.contains(mapping[vattr], dattrs);
    let openPosMappings = R$1.reject(isMapped, ['x', 'y']);
    let nonPosMappings = R$1.filter(isMapped, ['color', 'shape', 'column', 'size']);
    if (openPosMappings.length && nonPosMappings.length) {
      R$1.zip(openPosMappings, nonPosMappings).forEach(([openPos, nonPos]) => {
        newMapping[openPos] = mapping[nonPos];
        delete newMapping[nonPos];
      });
    }

    // ok now, map remaining attributes in order
    newDattrs = R$1.difference(dattrs, R$1.values(mapping));
    vattrs = R$1.difference(vattrs, R$1.keys(mapping));
    if (vattrs.length < newDattrs.length)
      throw new Error(`Too many new data variables, no visual variables to assign: ${newDattrs}`)
    R$1.zip(newDattrs, vattrs).forEach(([dattr, vattr]) => {
      newMapping[vattr] = dattr;
    });
    return newMapping;
  };


  me.dot = async (op, arg1, arg2) => {
    if (!arg1) {
      [arg1, arg2] = [arg2, null];
    }
    if (!arg1) return null;


    if (R$1.is(Array, arg1)) {
      if (!arg2) return me.naryDot(op, arg1)
      if (R$1.is(Array, arg2)) {
        return Promise.all(R$1.chain(
          (v1) => arg2.map((v2) => me.binaryDot(op, v1, v2)), 
          arg1
        ))
      }
      return Promise.all(arg1.map((v1) => me.binaryDot(op, v1, arg2)))
    }

    // arg1 is a View
    const v1 = arg1;
    if (!arg2) 
      return null;
    if (R$1.is(Array, arg2))
      return Promise.all(arg2.map((v2) => me.binaryDot(op, v1, v2)))
    return await me.binaryDot(op, v1, arg2)

  };

  me.getExprCardinalities = async (exprs, subq) => {
    "select count(distinct expr), ... from subq";
    
    let aliases = [];
    let counts = exprs.map((e, i) => {
      aliases.push(`a${i}`);
      return PClause({
        e: Func({ fname: "count", args:[e], distinct:true }),
        alias: `a${i}`
      })
    }
    );
    let q = Project({exprs: counts, child: subq});
    let rows = await runQuery(me.db, q.toSql().toString());
    let row = rows[0];
    return aliases.map((alias) => +row[alias]);
  };

  // return Agb attributes that have one distinct value
  // return: Array<str>
  me.getUnaryAgbs = async (v) => {
    let gbs = VCA.find(v.q, "GroupBy");
    if (gbs.length == 0) return [];
    let attrs = [];
    let AgbExprs = R$1.pluck("e", gbs[0].Agb);
    let cards = await me.getExprCardinalities(AgbExprs, gbs[0].c);
    R$1.zip(gbs[0].Agb, cards).forEach(([a, count]) => {
      if (count == 0) attrs.push(a);
    });
    return attrs;
  };

  //
  //
  //
  me.binaryDot = async (op, v1, v2) => {
    let match = me.getBinaryDotMatch(v1, v2);
    if (!match) {
      throw new Error("Views are not compatible")
    }

    match = R$1.omit([v1.mapping.measure], match);

    let lalias = newAlias(), 
        ralias = newAlias(),
        q1 = v1.q,
        q2 = v2.q;

    const isModel = (v) => v.q.classType == "Model";
    const toJoinCond = (match) => {
      let conds = R$1.toPairs(match).map(([lattr, rattr]) => {
        if (v1.mapping.measure == lattr) return null;
        return Expr({ op: "=", 
          l: Attr({table: lalias, attr: lattr}),
          r: Attr({table: ralias, attr: rattr})
        })
      });
      return R$1.reject(R$1.isNil, conds)
    };

    // XXX: fails when dragging cyl-mpg onto model view of cyl,hp->mpg
    // should be rejected since cyl does not fully schema match to cyl,hp.
    //
    // In general, if query-model join, then schema should fully match.
    // If query-query, then rigt side needs a full match, but not left side.

    // Type of join depends on whether v1/v2 are Models or not
    let on = toJoinCond(match);
    let join = null;
    if (isModel(v1) && isModel(v2)) {
      let bounds = mergeBounds(q1.bounds, q2.bounds);
      q1.setBounds(bounds);
      q2.setBounds(bounds);

      join = Join({
        l: q1, r: q2,
        lalias, ralias, on, bounds
      });
    } else if (isModel(v1) && !isModel(v2)) {
      join = ModelQueryJoin({
        l: q2, r: q1,
        lalias:newAlias(), ralias:newAlias()
      });
      join = Join({
        l: join, r: q2,
        lalias, ralias, on
      });
    } else if (!isModel(v1) && isModel(v2)) {
      join = ModelQueryJoin({
        l: q1, r: q2, 
        lalias: newAlias(), ralias: newAlias()
      });
      join = Join({
        l: q1, r: join,
        lalias, ralias, on
      });
    } else {
      let unaryAttrs = await me.getUnaryAgbs(v2);
      match = R$1.invertObj(R$1.omit(unaryAttrs,R$1.invertObj(match)));
      on = toJoinCond(match);
      console.log("dropped unary attrs:", unaryAttrs, "match:", match);
      console.log(on);
      join = Join({
        type: "outer",
        l: q1, r: q2, lalias, ralias, on
      });
    }

    let exprs = R$1.reject(
      (attr) => attr == v1.mapping.measure,
      R$1.pluck("attr", q1.schema())
    ).map((attr) => 
      PClause({ e: Attr({table: lalias, attr}), alias: attr}));
    exprs.push(PClause({
      e: VCA.parse(op.f(
        `${lalias}.${v1.mapping.measure}`, 
        `${ralias}.${v2.mapping.measure}`
      )),
      alias: v1.mapping.measure
    }));
    let q = Project({ exprs, child: join });

    // keep the visual mappings that q still can support
    let mapping = me.assignVisualMapping(q.schema(), v1.mapping);
    if (op.mark)
      mapping.mark = op.mark;
    console.log("new View mapping", mapping);

    return View({
      q,
      r: mapping,
      name: `${v1.viewName} ${op.label} ${v2.viewName}`,
      opts: {
        width: v1.width,
        height: v1.height,
        viewType: "composed"
      }
    })
  };

  me.naryDot = async (op, vs) => {
    // Drop gb attribute if unary in every view
    let allUnaryAttrs = await vs.map(me.getUnaryAgbs);
    let unaryAttrs = R$1.reduce(
      R$1.intersection, allUnaryAttrs[0], R$1.tail(allUnaryAttrs));

    // TODO: relax this verification
    if (!me.getNaryDotMatch(vs)) {
      console.error(vs);
      throw new Error("naryDot: could not find match or query not canonical form")
    }

    let children = vs.map((v) => v.q.c.clone());
    let union = Union({children});
    let copy = vs[0].q.clone();
    const Agb = R$1.reject((pc) => 
      R$1.contains(pc.alias, unaryAttrs), copy.Agb);

    const Fs = copy.Fs.map((pc) => {
      // take the arguments of the original agg function
      // and use op.f instead
      // e.g., f(a) --> op.f(a)
      const alias = pc.alias;
      const arg = pc.e.args[0];
      // TODO: change Attr table references in arg
      const e = Func({fname: op.f, args:[arg]});
      return PClause({e, alias})
    });
    
    let q = GroupBy({ Agb, Fs, child: union });
    return View({
      q, 
      r: vs[0].mapping, 
      name: `vset${id++}`,
      opts: {
        width: vs[0].width,
        height: vs[0].height,
        viewType: "composed"
      }

    })
  };


  me.union = async (op, args1, args2) => {
    if (R$1.is(Array, args1))
      return me.naryUnion(op, args1)
    if (args1.type == "View" && args2 && args2.type == "View")
      return me.naryUnion(op, [args1, args2])
    return null;
  };

  me.naryUnion = async (op, vs) => {
    let matches = me.getUnionMatch(vs);
    if (!matches) {
      console.error(vs);
      throw new Error("naryUnion: could not find match")
    }

    // XXX: The ordering of the projected clauses must be the same!
    let children = vs.map((v) =>  {
      let q = v.q.clone();
      let ops = VCA.find(q, ["GroupBy", "Project"]);
      let pc = PClause({
        e: Value({type: "Literal", value: v.id}),
        alias: 'qid'
      }); 
      if (ops.length == 0) {
        let exprs = [ ];
        return Project({ exprs, child: v.q })
      }
      if (ops[0].classType == "Project") 
        ops[0].pcs.push(pc);
      else {
        // wrap GroupBy in a Project so attr orderings are the same
        let exprs = ops[0].schema().map((A) => 
          PClause({ e: Attr(A.attr), alias: A.attr }));
        exprs.push(pc);
        return Project({ 
          exprs, 
          child: Source({ source: q, alias: newAlias()}) })
      }
      return q;
    });

    // Probably want to make qid a column-facet and swap nonmeasure
    // positional variable with column
    let union = Union({children});
    let mapping = me.assignVisualMapping(union.schema(), vs[0].mapping);
    let opts = {
      width: vs[0].width,
      height: vs[0].height,
      viewType: "composed"
    };

    if (mapping.column) {
      let cards = await me.getExprCardinalities([Attr(mapping.column)], union);
      opts.width = ((75 + 25) * cards[0]) + 125;
    }

    return View({
      q: union,
      r: mapping,
      name: newAlias("vset"),
      opts
    })
  };



  /*
   * op: { 
   *   Af,   -- Array<Attr>
   *   Ac,   -- Array<Attr>
   *   y,    -- Attr
   *   model -- str
   * } 
   */
  me.lift = async (op, v) => {
    let mapping = { mark: "line", measure: v.mapping.measure };
    if (!op.Af) {
      if (v.rmapping['y'] == v.mapping.measure)  // 1D
        op.Af = [Attr(v.mapping['x'])];
      else  // 2D
        op.Af = [Attr(v.mapping['x']), Attr(v.mapping['y'])];
    } else
      op.Af = R$1.flatten([op.Af]);

    op.Ac = R$1.reject(R$1.isNil, R$1.flatten([op.Ac]));

    if (op.Af.length == 0)
      mapping.mark = "bar";
    else if (op.Af.length == 2) 
      mapping.mark = "point";
    else if (op.Af.length > 2) 
      mapping.mark = "table";
    op.y = op.y || Attr(v.mapping.measure);

    let q = Model({
      child: v.q,
      Af: op.Af,
      Ac: op.Ac,
      y: op.y
    });
    
    let bounds = await getBounds(v.q, op.Af);
    q.setBounds(bounds);

    // train the model 
    await q.setup(me.db);


    // naive algorithm to assign visual vars
    const toAttrs = (A) => R$1.reject(R$1.isNil, R$1.pluck('attr',R$1.flatten([A])));
    let vattrs1 = ["x", "y"];
    let vattrs2 = ["color", "shape", "column"];
    op.Af.forEach((a,i) => {
      mapping[vattrs1[i]] = a.attr;
    });
    if (op.Af.length <= 1) {
      mapping.y = op.y.attr;
    } else {
      mapping.color = op.y.attr;
      vattrs2 = R$1.tail(vattrs2); // remove color from candidates
    }
    op.Ac.forEach((a,i) => {
      mapping[vattrs2[i]] = a.attr;
    });

    console.group("lift");
    console.log(`${toAttrs(op.Af)}->${op.y.attr} | ${toAttrs(op.Ac)}`);
    console.log(mapping);
    console.groupEnd();

    return View({
      q,
      r: mapping,
      name: `vset${id++}`,
      opts: {
        width: v.width,
        height: v.height,
        viewType: "composed"
      }
    })
  };


  // q: input query 
  // attrs: list of attributes to compute bounds for, or null to use all Af
  // 
  // returns: [[Attr, [min, max]], ...]
  let getBounds = async (q, attrs=null) => {
    let boundsq = squel$2.select()
      .from(q.toSql(), newAlias("bounds"));
    attrs = attrs || q.Af;
    attrs.forEach((a) => {
      boundsq.field(`min(${a.attr})`, `min_${a.attr}`);
      boundsq.field(`max(${a.attr})`, `max_${a.attr}`);
    });
    let res = await runQuery(me.db, boundsq.toString());
    let row = res[0];
    let bounds = attrs.map((a) => 
      [a, [row[`min_${a.attr}`], row[`max_${a.attr}`]]]
    );
    return bounds;
  };



  return me;
});


VCA.parse = parse;

// get all operators in query plan q where f(op) returns true
VCA.collect = (q, f) => {
  var ops = [];
  q.traverse((op) => {
    if (f(op) == true) ops.push(op);
  });
  return ops;
};

// get all operators in query plan with given class type
VCA.find = (q, classTypeOrTypes) => {
  if (R$1.is(String, classTypeOrTypes)) classTypeOrTypes = [classTypeOrTypes];
  return VCA.collect(q, (op) => R$1.contains(op.classType, classTypeOrTypes));
};

VCA.getAliases = (q) => R$1.pluck('attr', q.schema());
VCA.getAgb = (q) => {
  let gbs = VCA.find(q, "GroupBy");
  if (gbs.length == 0) return [];
  return gbs[0].Agb;
};

let ContextMenu = (({containerid, app}) => {
  let me = () => {};
  me.type = "ContextMenu";
  me.app = app;
  me.dom = $(`#${containerid}`);
  me.state = null;
  me.binaryCM = BinaryContextMenu({cm:me});
  me.naryCM = NaryContextMenu({cm:me});
  me.liftCM = LiftMenu({cm:me});

  me.render = (opts) => {
    me.dom.empty();
    if (me.state == "binary") {
      me.dom.append(me.binaryCM.render(opts).dom);
    } else if (me.state == "nary") {
      me.dom.append(me.naryCM.render(opts).dom);
    } else if (me.state == "lift") {
      me.dom.append(me.liftCM.render(opts).dom);
    }
    return me;
  };

  me.close = () => {
    me.state = null;
    me.render();
  };

  // user pressed enter key
  // @key string of pressed key
  me.onHotKey = (key) => {
    if (!me.state) return;

    if (me.state == "binary") {
      if (key == "Enter") 
        me.binaryCM.onLabel(me.binaryCM.selected.label);
      else if (key == "u") 
        me.onBinaryOp({type:"union"});
      else if (key == "-" || key == "+") 
        me.binaryCM.onLabel(key);
    } else if (me.state == "nary") {
      if (key == "Enter")
        me.naryCM.onLabel(me.naryCM.selected.label);
      else if (key == "u") 
        me.onNaryOp({type:"union"});
    } else if (me.state == "lift") {
      if (key == "Enter")
        me.liftCM.onLabel(me.liftCM.selected.label);

    }
  };

  me.onBinaryOp = (op) => me.app.onBinaryOp(op);
  me.onNaryOp = (op) => me.app.onNaryOp(op);
  me.onLift = (op) => me.app.onLift(op);

  return me;
});

let MarkContainer = ((marks, defaultMark) => {
  function me() {}
  me.type = "MarkContainer";
  me.marks = marks;   // list of mark names
  me.markEls = {};     // mark name -> jquery el
  me.chosen = null;   // the chosen mark to render
  me.dom = null;      // root jquery el

  me.render = () => {
    me.dom = $("<div class='mark-container'></div>");
    me.markEls = {};
    me.marks.forEach((mark) => {
      let el = $(`<input type='radio' name='mark' id='mark-${mark}' value='${mark}'/>`);
      let div = $("<div/>");
      div.append(el).append($(`<label for='mark-${mark}'>${mark}</label>`));
      div.on("click", () => me.choose(mark));
      me.dom.append(div);
      me.markEls[mark] = el;
      
      if (defaultMark == mark)
        el.click();
    });

    return me;
  };

  me.choose = (mark) => {
    if (me.markEls[mark]) ;
    me.chosen = mark;
    return me;
  };

  return me;
});



let BinaryContextMenu = (({cm}) => {
  const defaults = [
    {label: "+", f: (a1, a2) => `${a1} + coalesce(${a2}, 0)`},
    {label: "-", f: (a1, a2) => `${a1} - coalesce(${a2}, 0)`},
    {label: "min", f: (a1, a2) => `coalesce(least(${a1}, ${a2}), coalesce(${a1}, ${a2}))`},
    {label: "max", f: (a1, a2) => `coalesce(greatest(${a1}, ${a2}), coalesce(${a1}, ${a2}))`}
  ];
  let me = () => {};
  me.type = "BinaryContextMenu";
  me.cm = cm;
  me.dom = $("<div id='contextmenu-binary' class='contextmenu binary'></div>");
  me.selected = defaults[1];
  //me.markContainer = MarkContainer(['line', 'point', 'bar', 'table'])

  me.render = () => {
    me.dom.empty();
    me.dom.append($("<h3>Binary Stats</h3>"));
    defaults.forEach(({label, f}) => {
      let el = $(`<div class="btn btn-outline-primary operator">${label}</div>`);
      el.on("click", () => {
        $(".operator").addClass("btn-outline-primary").removeClass("btn-primary");
        el.removeClass("btn-outline-primary").addClass("btn-primary");
        me.onLabel(label);
      });
      if (me.selected.label == label)
        el.removeClass("btn-outline-primary").addClass("btn-primary");

      me.dom.append(el);
    });

    me.dom.append($("<h3>Union</h3>"));
    let el = $(`<div class="btn btn-outline-primary operator">Union</div>`);
    el.on("click", () => {
      me.cm.onBinaryOp({type:"union"});
    });
    me.dom.append(el);

    me.dom.append("<h3 style='margin-top: 1em;'>Mark Type</h3>");
    //me.dom.append(me.markContainer.render().dom)

    return me;
  };

  me.onLabel = (label) => {
    defaults.forEach(({label: l, f} ) => {
      if (l == label) 
        me.cm.onBinaryOp({label, f, type: "stats"});
    });
  };

  return me;
});


let NaryContextMenu = (({cm}) => {
  const defaults = [
    {label: "avg", f: "avg" },
    {label: "count", f: "count"},
    {label: "min", f: "min"},
    {label: "max", f: "max" }
  ];
  let me = () => {};
  me.type = "NaryContextMenu";
  me.cm = cm;
  me.dom = $("<div id='contextmenu-nary' class='contextmenu nary'></div>");
  me.selected = defaults[0];

  me.render = () => {
    me.dom.empty();
    me.dom.append($("<h3>Nary Stats</h3>"));
    defaults.forEach(({label, f}) => {
      let el = $(`<div class="btn btn-outline-primary operator">${label}</div>`);
      el.on("click", () => {
        $(".operator").addClass("btn-outline-primary").removeClass("btn-primary");
        el.removeClass("btn-outline-primary").addClass("btn-primary");
        me.onLabel(label);
      });
      if (me.selected.label == label)
        el.removeClass("btn-outline-primary").addClass("btn-primary");

      me.dom.append(el);
    });

    me.dom.append($("<h3>Union</h3>"));
    let el = $(`<div class="btn btn-outline-primary operator">Union</div>`);
    el.on("click", () => {
      me.cm.onNaryOp({type:"union"});
    });
    me.dom.append(el);

    return me;
  };

  me.onLabel = (label) => {
    defaults.forEach(({label: l, f} ) => {
      if (l == label) 
        me.cm.onNaryOp({label, f, type: "stats"});
    });
  };



  return me;
});





let LiftMenu = (({cm}) => {
  const defaults = [
    {label: "linear"},
    {label: "logistic"},
    //{label: "poly", n: 3},
    {label: "glm"}
  ];
  let me = () => {};
  me.type = "LiftMenu";
  me.cm = cm;
  me.dom = $("<div id='contextmenu-lift' class='contextmenu lift'></div>");
  me.selected = defaults[1];

  me.Af = {};
  me.Ac = {};
  me.measure = null;

  me.render = ({v}) => {
    me.dom.empty();
    me.dom.append($("<h3>Lift</h3>"));
    defaults.forEach(({label, f}) => {
      let el = $(`<div class="btn btn-outline-primary operator">${label}</div>`);
      el.on("click", () => {
        $(".operator").addClass("btn-outline-primary").removeClass("btn-primary");
        el.removeClass("btn-outline-primary").addClass("btn-primary");
        me.onLabel(label);
      });
      if (me.selected.label == label)
        el.removeClass("btn-outline-primary").addClass("btn-primary");

      me.dom.append(el);
    });

    me.dom.append($("<h3>Attributes</h3>"));
    let table = $("<table class='table table-striped lift'></table>");
    me.dom.append(table);
    let tbody = $("<tbody></tbody>");
    tbody.append($("<tr><th>Feature</th><th>Condition</th><th></th></tr>"));
    table.append(tbody);
    console.group("liftmenu");
    v.q.schema().forEach((a) => {
      if (a.attr == v.mapping.measure) {
        me.measure = a;
        return;
      }
      tbody.append(me.renderAttribute(a, v));
      console.log(R.keys(me.Af));
    });
    console.groupEnd();

    return me;
  };

  // return <tr>
  me.renderAttribute = (a, v) => {
    let tr = $("<tr/>");
    let td1 = $("<td/>");
    let td2 = $("<td/>");
    let td3 = $("<td/>");
    let cb1 = $("<input class='af' type='checkbox'/>");
    let cb2 = $("<input class='ac' type='checkbox'/>");
    td1.append(cb1);
    td2.append(cb2);
    td3.append($(`<span>${a.attr}</span>`));

    cb1.on("click", (e) => {
      if (cb1[0].checked) {
        me.Af[a.attr] = a;
        delete me.Ac[a.attr];
        cb2[0].checked = false;
      } else {
        delete me.Af[a.attr];
      }
    });
    cb2.on("click", (e) => {
      if (cb2[0].checked) {
        me.Ac[a.attr] = a;
        delete me.Af[a.attr];
        cb1[0].checked = false;
      } else {
        delete me.Ac[a.attr];
      }
    });

    if (v.mapping['x'] == a.attr) 
      cb1.click();

    tr.append(td1);
    tr.append(td2);
    tr.append(td3);
    return tr;
  };

  me.onLabel = (label) => {
    defaults.forEach((op) => {
      if (op.label != label) return;
      op = R.clone(op);
      op.model = op.label;
      op.Af = R.values(me.Af);
      op.Ac = R.values(me.Ac);
      op.y = me.measure;
      me.cm.onLift(op);
    });
    me.Af = {};
    me.Ac = {};
    me.measure = null;

  };

  return me;
});

let VegaliteView = (({view, dom, mapping, opts}) => {
  let id = 0;
  let newAlias = (prefix="t") => `${prefix}${id++}`;

  let me = () => {};
  me.view = view;

  me.dom = dom;
  me.vlview = null;
  me.spec = null;
  me.data = [];
  me.selection = {};
  me.opts = opts || {};
  me.width = opts.width || 200;
  me.height = opts.height || 200;

  me.dataChanged = false;
  me.shouldRefresh = false;

  me.setData = (data) => {
    me.data = data;
    me.dataChanged = true;
  };

  me.init = () => {
  };

  me.render = () => {
    if (me.vlview && me.dataChanged) { // update
      let changeset = vega.changeset()
        .remove(()=>true)
        .insert(me.data);
      me.vlview.view.change('data', changeset).run();
      me.dataChanged = false;
    } 

    if (!me.vlview || me.shouldRefresh)  { // create
      me.spec = genSpec(me.data);
      console.log(me.spec);
      vegaEmbed(me.dom[0], me.spec, {renderer: "svg"})
        .then(vegaOnLoad);
      me.shouldRefresh = false;
    }
  };


  // XXX: if view is faceted, we can't figure out which facet the user 
  //      is selecting within!
  me.onNewView =  async (e) => {
    if (R$1__default.keys(me.selection).length == 0) return;
    e.preventDefault();
    console.log("newviewbtn: ", me.selection);
    let predicates = [];
    R$1__default.forEachObjIndexed((bound, dattr) => {
      let vattr = me.view.rmapping[dattr];
      let type = me.spec.encoding[vattr] && me.spec.encoding[vattr].type;

      if (type == "quantitative") { // min <= attr && attr < max
        predicates.push(Expr({
          op: ">=", l: Attr(dattr), r: Value({value: bound[0]})
        }));
        predicates.push(Expr({
          op: "<", l: Attr(dattr), r: Value({value: bound[1]})
        }));
      } else {  // attr IN (...)
        let args = bound.map((v) => Value({value: v})).map((V) => V.toSql()).join(",");
        predicates.push(Expr({
          op: "IN",
          l: Attr(dattr),
          r: Value({value: `(${args})`, raw: true})
        }));
      }
    }, me.selection);

    let newq = Where({
      exprs: predicates,
      child: Source({ source: me.view.q, alias: newAlias('newview')})
    });

    // TODO: drop non positional attrs that are unary
    let mapping = R$1__default.clone(me.view.mapping);
    let exists = (attr) => me.view.mapping[attr];
    let attrs = R$1__default.filter(exists, ["column", "color", "shape", "size"])
      .map((vattr) => Attr(me.view.mapping[vattr]));
    let cards = await me.view.viewManager.app.VCA.getExprCardinalities(attrs, newq);
    R$1__default.zip(attrs, cards).forEach(([dattr, card]) => {
      if (card == 0) 
        delete mapping[me.view.rmapping[attr]];
    });

    let v = View({
      q: newq,
      r: mapping,
      name: `${me.view.viewName}[${predicates.map((p) => p.toSql()).join(",")}]`
    });
    await me.view.viewManager.addView(v);
  };


  function genSpec(data) {
    var spec = {
      width: me.width,
      height: me.height,
      autosize: {
        type: "fit",
        contains: "padding",
        resize: true
      },
      data: { name: "data", values: data },
      mark: me.view.mapping["mark"] || "bar", 
      axis: {
        titleFontSize: 30,
        labelFontSize: 30
      },
      encoding: {},
      params: []
    };
    let mapping = me.view.mapping;

    if (me.view.isCompositionMode()) {
      let selection = {
        name: "selection",
        select: {
          type: "interval",
          on:  "[mousedown[event.shiftKey], mouseup] > mousemove",
          translate: "[mousedown[event.shiftKey], mouseup] > mousemove!"
        }
      };

      if (mapping.y == mapping.measure && mapping.x) {
        selection.select.encodings = ["x"];
      } else if (mapping.x == mapping.measure && mapping.y) {
        selection.select.encodings = ["y"];
      } else if (!mapping.x || !mapping.y) {
        selection = null;
      }
      if (selection)
        spec.params.push(selection);
    }

    R$1__default.forEach(([vattr, dattr]) => {
      if (vattr == "measure" || vattr == "mark") return;
      spec.encoding[vattr] = {
        axis: {
          title: dattr || vattr,
          titleFontSize: 18,
          labelFontSize: 14,
          titleFontWeight: "normal",
          labelOverlap: "parity"
        },
      };
      if (vattr == "color") {
        let type = (dattr == mapping.measure)? "quantitative" : "nominal";
        spec.encoding[vattr].field = dattr;
        spec.encoding[vattr].type = type;
      } else {
        spec.encoding[vattr].field = dattr;
        spec.encoding[vattr].type = getType(dattr, vattr, spec.mark);
      }
    }, R$1__default.toPairs(mapping));


    if (mapping["column"]) {
      let n = R$1__default.uniq(R$1__default.pluck(mapping["column"], me.data)).length;
      spec.width = me.width - 100;
      if (n > 1) 
        spec.width = (spec.width / n) - 10;
      spec.height = (me.height - 120);
    }

    return spec;
  }

  function isNumber(v) {
    return !Number.isNaN(+v);
  }


  function getType(dataAttr, visAttr, mark) {
    if (visAttr == "x") {
      if (mark == "line" || mark == "point") {
        if (isNumber(me.data[0][dataAttr]))
          return "quantitative"
      }
      return "ordinal"
    }
    if (visAttr == "column") return "ordinal"
    if (visAttr == "color") {
      if (dataAttr == "qid") return "ordinal"
      if (isNumber(me.data[0][dataAttr])) return "quantitative"
      return "ordinal"
    }
    return "quantitative"
  }

  const vegaOnLoad = (p) => {
    p.view.preventDefault(false);
    me.vlview = p;

    const handler = me.view.viewManager.composeHandler;
    p.view.addEventListener("pointerdown", (e, i) => {
      if (e.shiftKey) return;
      if (!(i && i.datum)) return;
      const thumb = $$1("<svg><g></g></svg>");
      thumb.children(0).append($$1(e.srcElement).clone());
      handler.onStart(e, datumToOperand(e,i), thumb);
      e.stopPropagation();
    });
    p.view.addEventListener("pointermove", (e, i) => {
      if (!(i && i.datum)) return;
      handler.onMove(e, datumToOperand(e,i));
      e.stopPropagation();
    });
    p.view.addEventListener("pointerup", (e, i) => {
      handler.onDrop(e, datumToOperand(e,i));
      e.stopPropagation();
    });
    if (me.view.isCompositionMode() && p.view._signals["selection"]) {
      p.view.addSignalListener("selection", (e, i) => {
        if (R$1__default.keys(i).length == 0) {
          me.view.btn_newview.addClass("disabled");
          return; 
        }
        me.view.btn_newview.removeClass("disabled");
        me.selection = i;
      });
    }

  };


  const datumToOperand = (e, i) => {
	return { 
	  type: "Mark",
	  data: datumToView(i),
	  svg: $$1(e.srcElement),
	  view: me.view
	}
  };


  const datumToView = (i) => {
	if (!(i && i.datum)) return null;
    // turn datum into a 0-dimensional View object
    // that only contains the data attribute mapped to y
    const dattr = me.view.mapping.measure;
    const yval = i.datum[dattr];
    const pc = PClause({ e: Value({value: yval}), alias: dattr});
    const Fs = [pc];

    //const Fs = R.reject(R.isNil, 
	//  R.map(([k, v]) => {
	//	if (k == "Symbol(vega_id)" || k == "__proto__") return;
	//	return PClause({ e: Value({value: v}),  alias: k})
	//  }, R.toPairs(i.datum)))

    const q = Project({exprs: Fs });
    return View({ 
      q, 
      r: R$1__default.pick(["y", "measure"], me.view.mapping),
      name: yval,
      opts: R$1__default.clone(me.view.opts)
    })

  };




  return me;

});

let TableView = (({dom, view, mapping, opts}) => {
  let me = () => {};
  me.view = view;

  me.dom = dom;
  me.data = [];
  me.mapping = mapping; 
  me.opts = opts || {};
  me.width = opts.width || 200;
  me.height = opts.height || 200;

  me.setData = (data) => me.data = data;

  me.init = () => {
  };

  me.render = () => {
    me.dom.empty();

    const table = $$1("<table class='table table-striped disable-select tableview'>");
    const header = $$1("<tr></tr>");
    const body = $$1("<tbody></tbody>");
    table
      .append(header)
      .append(body);

    let tablehandle = $$1("<th></th>");
    header.append(tablehandle);
    let keys = R$1__default.keys(me.data[0]);
    keys.forEach((v) =>
      header.append($$1(`<th>${v}</th>`))
    );

    me.data.forEach((row) => {
      let tr = $$1("<tr></tr>");
      let rowhandle = $$1("<td>&Xi;</td>");
      if (!me.view.isCompositionMode())
        rowhandle = $$1("<td/>");
      tr.append(rowhandle);

      keys.forEach((key) => {
        let cell = $$1(`<td>${row[key]}</td>`);
        tr.append(cell);
        if (me.view.isCompositionMode())
          addCellListeners(cell, key, row[key]);
      });

      if (me.view.isCompositionMode())
        addRowListeners(rowhandle, tr, row);
      body.append(tr);
    });


    me.dom.append(table);
    me.dom.css({
      overflow: "scroll",
      height: "85%"
    });
  };

  const addTableListeners = (el, data, thumb) => {
    el.addClass("table-handle").addClass("enabled");


    const handler = me.view.viewManager.composeHandler;
    el[0].addEventListener("pointerdown", (e, i) => {
      handler.onStart(e, data, thumb);
    });
    el[0].addEventListener("pointermove", (e) => {
      handler.onMove(e, data);
    });
    el[0].addEventListener("pointerup", (e) => {
      handler.onDrop(e, data);
    });

  };


  const addCellListeners = (cell, attr, val) => {
    const Fs = [PClause({ e: Value({value: val}), alias: attr })];
    const q = Project({exprs: Fs});
    const v = View({q, r:{ y:attr, measure:attr }, name: val});
    const data = {
      type: "Mark",
      data: v,
      svg: cell,
      view: me.view
    };

    const thumb = $$1("<div class='table-thumb'></div>");
    thumb.append($$1(cell).clone());
    addTableListeners(cell, data, thumb);
  };

  const addRowListeners = (td, tr, row) => {
    const Fs = [];
    R$1__default.forEachObjIndexed((dattr, vattr) => {
      if (row[dattr] !== undefined)
        Fs.push(PClause({
          e: Value({ value: row[dattr] }),
          alias: dattr
        }));
    }, me.mapping);
    const q = Project({exprs: Fs});
    const v = View({q, r:R$1__default.clone(me.mapping), name: row[me.view.mapping.measure]});
    const data = {
      type: "Mark",
      data: v,
      svg: td,
      view: me.view
    };
    const thumb = $$1("<div class='table-thumb'></div>");
    const table = $$1("<table></table>");
    thumb.append(table);
    table.append(tr.clone());
    addTableListeners(td, data, thumb);
  };

  return me;
});

let MapView = (({dom, view, opts}) => {

  let me = () => {};
  me.dom = dom;
  me.view = view;
  me.opts = opts || {};
  me.height = (me.opts.height)? `${me.opts.height}px` : "100%";
  me.style = () => {};
  me.statesData = null;
  me.map = null;

  me.setData = (data) => {
    let stateCounts = {};
    data.forEach(({state, count}) => 
      stateCounts[state] = +count);
    me.statesData.features.forEach((feat) => {
      if (stateCounts[feat.properties.name])
        feat.properties.count = stateCounts[feat.properties.name];
    });
    
    let counts = R$1__default.values(stateCounts);
    let [minc, maxc] = [.1, .9];
    if (R$1__default.any((c) => c<0, counts)) {
      minc = d3.min(counts);
      maxc = d3.max(counts);
      const absmax = Math.max(Math.abs(minc), Math.abs(maxc));
      minc = -absmax;
      maxc = absmax;
    }
    console.log("min, max", minc, maxc);
    
    let domain = R$1__default.times((v) => (maxc-minc)/8.0 * v + minc, 8);
    let range = ["#b2182b","#d6604d","#f4a582","#fddbc7","#d1e5f0","#92c5de","#4393c3","#2166ac"];
    let color = d3.scaleLinear().domain(domain).range(range);

    me.style = (feature) => {
      let count = feature.properties.count;
      return {
          fillColor: color(count) || 'white',
          weight: 2,
          opacity: 1,
          color: 'white',
          dashArray: '3',
          fillOpacity: 0.7
      };
    };
  };

  me.init = () => {
    me.statesData = R$1__default.clone(statesData);
    me.dom.css({
      width: `100%`,
      height: me.height
    });

  };

  // assumes statesData is a global variable...
  // assumes schema: (state, value)
  me.render = (data) => {
    if (!me.map) {
      me.map = L.map(me.dom[0]).setView([37.8, -96], 3);
    }

    me.map.eachLayer((layer) => layer.remove());

    //L.tileLayer('https://api.mapbox.com/styles/v1/{id}/tiles/{z}/{x}/{y}?access_token=' + accessToken, {
    //      id: 'mapbox/light-v9',
    //      tileSize: 512,
    //      zoomOffset: -1
    //}).addTo(me.map);
    L.geoJson(me.statesData).addTo(me.map);
    L.geoJson(me.statesData, {style: me.style}).addTo(me.map);
  };

  return me;
});

/*
 * q: query plan
 * r: { vis attr : data attr name, measure: data attr name }
 *    r MUST contain "measure" so we know which vis attribute
 *    is encoding the measure variable
 *
 * TODO: support axis labels and other configurations in r
 */
function View({q, r, id, name, opts}) {
  const visualVars = ["x", "y", "color", "size"];

  function me(){}  me.type = "View";
  me.dom = null;
  me.viewManager = null;
  me.data = null;
  me.q = q;
  me.mapping = r;
  me.id = id;
  me.viewName = name;
  me.opts = opts || {};
  me.width = me.opts.width || 500;
  me.height = me.opts.height || 350;
  me.viewType = me.opts.viewType; // null if base view, else composed

  me.subview = null;
  me.mappingEditMenu = null;
  me.explodeMenu = null;

  me.btn_newview = null;
  me.map = null;
 

  if (!me.mapping['measure']) {
    throw new Error("View: mapping must contain measure:", me.mapping)
  }

  me.setViewManager = (viewManager) => {
    me.viewManager = viewManager;
  };

  me.isCompositionMode = () => 
    (me.viewManager)? me.viewManager.app.isCompositionMode() : false;

  me.setCompositionMode = (mode) => {
    me.subview.shouldRefresh = true;
  };

  me.setMapping = (mapping) => {
    me.mapping = mapping;
    resolveMapping();
    me.vldiv.empty();

    // create the subviews
    let args = {
      dom: me.vldiv,
      view: me,
      mapping: me.mapping,
      opts: {
        width: me.width - 50,
        height: me.height - 50
      }
    };
    me.subview = getViewFromMark(me.mapping.mark)(args);
    me.subview.init();
    me.subview.setData(me.data);
  };

  const getViewFromMark = (mark) => {
    if (mark == "map") 
      return MapView
    else if (mark == "table")
      return TableView
    return VegaliteView
  };

  // If there are any unmapped data attributes, bind them
  // Then update the reverse visual mapping
  function resolveMapping() {
    // temporary 
    let rmapping = R$1__default.invertObj(R$1__default.omit(["measure"], me.mapping));
    let dattrs = R$1__default.pluck("attr", me.q.schema())
      .filter((dattr) => !rmapping[dattr]);

    // first fill out exact mappings e.g., x->x
    dattrs.forEach((dattr) => {
      if (R$1__default.contains(dattr, availVars())) 
        me.mapping[dattr] = dattr;
    });

    // then assign mappings to remaining data attrs
    dattrs.forEach((dattr) => {
      if (!me.mapping[dattr]) {
        let vattr = assignMapping(dattr);
        me.mapping[vattr] = dattr;
      }
    });

    me.rmapping = R$1__default.invertObj(R$1__default.omit(["measure"], me.mapping));
  }

  function availVars() {
    return visualVars.filter((v) => !me.mapping[v]);
  }

  function assignMapping(alias) {
    if (R$1__default.contains(alias, availVars())) return alias;
    return availVars()[0];
  }

  me.init = () => {
    if (me.dom) return;
    const mark = me.mapping.mark;

    const dom = $$1(`<div class="col"></div>`);
	const holder = $$1(`<div class="holder"></div>`);
    const title = $$1(`<div class="title ${me.viewType? "composed" : ""}">${me.viewName}</div>`);
    const rightmenu = $$1("<span class='rightmenu'></span>");
    const newview = $$1(`<span class='newview' data-toggle="tooltip" data-placement="top" title="Turn selection into a new view"></span>`).addClass("disabled");
    const explode = $$1(`<span class='explode' data-toggle="tooltip" data-placement="top" title="Facet this view">&Xi;</span>`);
    const edit = $$1(`<span class='edit' data-toggle="tooltip" data-placement="top" title="Edit visual mappings"></span>`);
    const lift = $$1(`<span class='lift' data-toggle="tooltip" data-placement="top" title="Lift view into a model"></span>`);
    const close = $$1(`<span class="close"  data-toggle="tooltip" data-placement="top" title="Remove this view"></span>`);
    const div = $$1(`<div id="${me.id}"></div>`);

    const nonposVattrs = ["color", "size", "column", "shape"].filter((vattr) => 
      me.mapping[vattr] && me.mapping[vattr] != me.mapping.measure
    );
    
    title.append(rightmenu);
    rightmenu.append(close);
    rightmenu.append(edit);
    if (mark != "map") rightmenu.append(lift);
    if (nonposVattrs.length > 0) rightmenu.append(explode);
    rightmenu.append(newview);
    holder.append(title);
    holder.append(div);
	dom.append(holder);
    holder.css({
      width: me.width,
      height: me.height
    });

    me.title = title;
    me.vldiv = div;    // div that vegalite will render into
	me.holder = holder;
    me.dom = dom;
    me.btn_newview = newview;
    registerViewHandlers();

    // create the subviews
    let args = {
      dom: me.vldiv,
      view: me,
      mapping: me.mapping,
      opts: {
        width: me.width - 50,
        height: me.height - 50
      }
    };
    me.subview = getViewFromMark(mark)(args);
    me.subview.init();


    newview.tooltip();
    explode.tooltip();
    edit.tooltip();
    lift.tooltip();
    close.tooltip();



    close.on("click", (e) => { 
      if (me.viewManager) {
        e.stopPropagation();
        me.viewManager.onRemoveHandler(me);
      }
    }); 

    edit.on("click", (e) => {
      e.stopPropagation();
      $$1("#contextmenu-container").append(me.mappingEditMenu.render().dom);
    });
    
    if (mark != "map")
      lift.on("click", (e) => {
        if (me.viewManager) {
          me.viewManager.app.onLiftView(me);
          e.preventDefault();
        }
      });

    explode.on("click", (e) => {
      $$1("#contextmenu-container").append(me.explodeMenu.render().dom);
    });

    if (me.subview.onNewView)
      newview.on("click", me.subview.onNewView);

    me.explodeMenu = ExplodeMenu({v:me, vattrs:nonposVattrs}).init();
    me.mappingEditMenu = MappingEditMenu({v:me}).init();
  };

  me.updateQuery = (q) => {
    me.data = null;
    me.q = q;
  };


  // a view is responsible for 
  // * updating its visual state throughout an interaction
  //   its states can be unselected, selected, hovered
  // * providing a View object to represent an operand
  // The actual interaction logic is managed by the viewmanager in views.js
  me.interactionState = null;

  const registerViewHandlers = () => {
    const handler = me.viewManager.composeHandler;
    me.holder[0].addEventListener("pointerup", (e) => {
	  handler.onDrop(e, {type: "View", data: me, view: me});
    });
	me.dom[0].addEventListener("pointerup", (e) => {
	  if (me.dom[0] != e.target) return;
	  handler.onDrop(e, null);
	});
	me.dom[0].addEventListener("pointermove", (e) => {
	  if (me.dom[0] != e.target) return;
	  me.viewManager.onMoveViews(e);
	});
	me.holder[0].addEventListener("pointermove", (e) => {
	  handler.onMove(e, { type: "View", data: me, view: me });
	});
    me.title[0].addEventListener("pointerdown", (e) => {
	  if (descendantOfClass(e.target, "close")) return;
      if (e.button != 0) return;
	  handler.onStart(e, { type: "View", data: me, view: me }, me.vldiv.clone());
    });
  };

  me.render = async () => {
    if (!me.data) {
      me.data = await runQuery(me.viewManager.app.db, me.q.toSql().toString());
      me.subview.setData(me.data);
    }
    me.subview.render(me.data);
    return me;
  };

  resolveMapping();
  return me;
}


let ExplodeMenu = (({v, vattrs}) => {
  let me = () => {};
  me.dom = $$1("<div></div>");
  me.view = v;
  me.vattrs = vattrs;
  me.chosen = null;

  me.init = () => {
    return me;
  };

  me.clear = () => {
    me.dom.empty();
    me.chosen = null;
    me.dom[0].remove();
    return me;
  };

  me.render = () => {
    me.dom.empty();
    me.dom.append($$1("<h3>Choose Attr to Explode</h3>"));

    me.inputs = {};
    me.vattrs.map((vattr) => {
      let dattr = me.view.mapping[vattr];
      let el = $$1("<div/>");
      let input = $$1(`<input type='radio' id='r-${dattr}' name='explodemenu'/>`);
      let label = $$1(`<label for='r-${dattr}' style='margin-left: 1em;'>${dattr}</label>`);
      el.append(input).append(label);
      me.dom.append(el);

      input.on("input", () => {
        me.chosen = dattr;
      });
      return input;
    });

    let btn = $$1("<button>Explode</button>");
    btn.on("click", async () => {
      if (!me.chosen) return;
      let views = await me.view.viewManager.facetView(me.view, me.chosen);
      await me.view.viewManager.addViews(views);
      me.clear();
    });
    me.dom.append(btn);

    return me;
  };
  return me;
});
 

let MappingEditMenu = (({v}) => {
  let me = () => {};
  me.dom = $$1("<div></div>");
  me.mc = null;

  me.init = () => {
    let marks = ["line", "bar", "point", "table"];
    let dattrs = R$1__default.pluck("attr", v.q.schema());
    if (R$1__default.all((dattr) => R$1__default.contains(dattr, ["state", "count"]), dattrs))
      marks.push("map");
    console.log(v.mapping.mark);
    me.mc = MarkContainer(marks, v.mapping.mark);
    return me;
  };

  me.clear = () => {
    me.dom.empty();
    me.dom[0].remove();
  };

  me.render = () => {
    me.dom.empty();
    let vattrs = ['x', 'y', 'color', 'shape', 'column', 'size' ]; 
    let selects = {};

    me.dom.append($$1("<h3>Marks</h3>"));
    me.dom.append(me.mc.render().dom);

    me.dom.append($$1("<h3>Visual Mappings</h3>"));
    for (let A of v.q.schema()) {
      let dattr = A.attr;
      let el = $$1("<div class='row'/>");
      let label = $$1(`<div style='display: inline; text-align: right; width: 15em;'>${dattr}</div>`);
      let select = $$1("<select/>");
      for (let vattr of vattrs) {
        let option = $$1(`<option value='${vattr}'>${vattr}</option>`);
        select.append(option);
      }
      console.log(v.rmapping[dattr]);
      select.val(v.rmapping[dattr]);
      el
        .append($$1("<div class='col-md-4'/>").append(label))
        .append($$1("<div class='col-md-8'/>").append(select));
      me.dom.append(el);
      selects[dattr] = select;
    }

    let btn = $$1("<button style='margin-top: 1em'>Update Mapping</button>");
    btn.on("click", () => {
      let mapping = {
        mark: me.mc.chosen,
        measure: v.mapping.measure
      };
      for (let [dattr, select] of R$1__default.toPairs(selects)) {
        let vattr = select.val();
        if (mapping[vattr]) {
          debug(`${vattr} already mapped to ${mapping[vattr]}`);
          return
        }
        mapping[vattr] = dattr;
      }
      console.log(mapping);
      v.setMapping(mapping);
      v.render();
      me.clear();
    });
    me.dom.append(btn);

    return me;
  };
  return me
});

//
// For dragging from data shelf to encoding shelf
//
let ViewCreateHandler = (() => {
  let tableAttrData = null;  // { table, attr, type }
  let body = document.body;
  let dragImage = $(`<div class="drag-image-container button btn-light"></div>`);
  body.appendChild(dragImage[0]);

  let me = (e, type, data) => {
    if (!data || (data.type != "DataShelf" && data.type != "DropZone")) 
      return;
    if (type == "start")
      start(e, type, data);
    else if (type == "drop")
      drop(e, type, data);
    else if (type == "dragover")
      over(e, type, data);
    else if (type == "enter")
      enter(e, type, data);
    else if (type == "leave")
      leave(e, type, data);
    else if (type == "end")
      end(e);
  };

  function start(e, type, data) {
    dragImage.text(data.attr);
    e.dataTransfer.setDragImage(dragImage[0], 100, 0);
    tableAttrData = data;
    $(".encshelf-drop").addClass("dragstart");
  }
  function end(e) {
    e.preventDefault();
    $(".encshelf-drop").removeClass("dragover");
    $(".encshelf-drop").removeClass("dragstart");
    tableAttrData = null;
  }
  function drop(e, type, shelf) {
    if (!tableAttrData) return;
    e.preventDefault();
    e.dataTransfer.dropEffect = "move";
    shelf.addDataAttr(tableAttrData);
    $(".encshelf-drop").removeClass("dragover");
    $(".encshelf-drop").removeClass("dragstart");
  }
  function over(e, type, shelf) {
    e.preventDefault();
    if (shelf.dataAttr) return;
    $(".encshelf-drop").removeClass("dragover");
    $(shelf.dropzoneEl).addClass("dragover");
  }
  function enter(e, type, shelf) {
    e.preventDefault();
    if (shelf.dataAttr) return
    shelf.dropzoneEl.addClass("dragover");
  }
  function leave(e, type, shelf) {
    e.preventDefault();
    shelf.dropzoneEl.removeClass("dragover");
  }

  return me;
});



//
// For VCA interactions
//
let ComposeHandler = ((viewManager) => {
  const me = () => {};
  me.viewManager = viewManager;
  me.app = viewManager.app;
  me.srcOperand = null;
  me.thumbDiv = null;

  const updateThumbPosition = (e) => {
	if (!me.thumbDiv) return;
	me.thumbDiv.css({
	  left: `${e.pageX + 30}px`,
	  top: `${e.pageY + 30}px`
	});
  };


  me.onStart = (e, src, thumb) => {
	if (!me.viewManager.app.isCompositionMode()) return;
	if (!src) return;

	console.info("Iact.onStart src", src);
	me.srcOperand = src;
	me.viewManager.selectionHandler.reset();
	if (src.type == "Viewset")
	  me.viewManager.selectViews(null, true);
	else
	  me.viewManager.selectViews(null);


	// update visuals
	if (src.type == "View") {
	  src.data.holder.addClass("anchor");
	  me.viewManager.dom[0].setPointerCapture(e.pointerId);
	} else if (src.type == "Mark") {
	  setAndSaveCss(src.svg, { stroke: "red" });
	} else if (src.type == "Viewset") {
	  src.dom.addClass("anchor");
	}
	
	if (thumb) {
	  me.thumbDiv = $("<div id='thumb'></div>");
	  $("html").append(me.thumbDiv);
	  me.thumbDiv.append(thumb);
	  updateThumbPosition(e);
	}
  };

  me._prevOnMoveData = null;
  me.onMove = (e, data) => {
	if (!me.viewManager.app.isCompositionMode()) return;
	if (!me.srcOperand) return;
	$(".holder").removeClass("dragover");
	$("#newviewdrop").removeClass("dragover");
	updateThumbPosition(e);

	if (me._prevOnMoveData &&
	    !(data && data.type == "Mark" &&
 	      data.svg[0] == me.srcOperand.svg[0])) {
	  restoreCss(me._prevOnMoveData.svg, ["stroke"]);
	}

	if (!data) return;
	if (data.type == "Mark") {
	  if (me.srcOperand.type == "Mark" && data.data) {
		setAndSaveCss(data.svg, { stroke: "red" });
		if (data.svg[0] != me.srcOperand.svg[0]) 
		  me._prevOnMoveData = data;
		else
		  me._prevOnMoveData = null;
	  } else if (me.srcOperand.type == "View") {
		// treat mark as a view instead
		me._prevOnMoveData = null;
		if (me.srcOperand.view != data.view) {
		  data.view.holder.addClass("dragover");
		}
	  }
	} else if (data.type == "View") {
	  if (me.srcOperand.type == "Mark") {
		if (me.srcOperand.view != data.view) {
		  data.view.holder.addClass("dragover");
		}
	  } else if (me.srcOperand.type == "View") {
		if (me.srcOperand.view != data.view) {
		  data.view.holder.addClass("dragover");
		}
	  }  else if (me.srcOperand.type == "Viewset") {
		data.view.holder.addClass("dragover");
	  }
	} else if (data.type == "Create") {
      $("#newviewdrop").addClass("dragover");
    }

	e.stopPropagation();
  };


  // only views can be targets currently
  // @tgt: { type: "View", "Mark", or "Create", 
  //         data: View or null }
  //        type="Create" turns srcOperand into a new View
  //        the src Operand cannot be a viewset
  me.onDrop = (e, tgt) => {
	if (!me.viewManager.app.isCompositionMode()) return;
	if (!me.srcOperand) return;

	// reset visuals
	console.info("Iact.onDrop target", tgt, "src", me.srcOperand);
	$(".holder").removeClass("dragover").removeClass("anchor");
	$("#newviewdrop").removeClass("dragover");
	$("#viewsetdrop").removeClass("anchor");
	if (me.srcOperand.type == "Mark") {
	  restoreCss(me.srcOperand.svg, ["stroke"]);
	} 
	if (me._prevOnMoveData) {
	  restoreCss(me._prevOnMoveData.svg, ["stroke"]);
	  me._prevOnMoveData = null;
	}
	if (me.thumbDiv) {
	  me.thumbDiv[0].remove();
	  me.thumbDiv = null;
	}

	me.viewManager.dom[0].releasePointerCapture(e.pointerId);
	if (tgt) {
	  if (tgt.type == "View") {
		if (me.srcOperand.type == "View" && me.srcOperand.data != tgt.data) {
		  me.app.onComposeView(tgt.data, me.srcOperand.data);
		} else if (me.srcOperand.type == "Mark") {
		  me.app.onComposeView(tgt.data, me.srcOperand.data);
		} else if (me.srcOperand.type == "Viewset") {
		  me.app.onComposeView(tgt.data, me.srcOperand.data);
		}
	  } else if (tgt.type == "Mark") {
		if (me.srcOperand.type == "Mark" && me.srcOperand.svg[0] != tgt.svg[0]) {
		  me.app.onComposeView(tgt.data, me.srcOperand.data);
		} else if (me.srcOperand.type == "View") {
		  // treat target as a view instead
		  console.info("Iact.onDrop: mark target -> View", me.srcOperand.view.id, tgt.view.id);
		  if (me.srcOperand.view != tgt.view) {
			me.app.onComposeView(tgt.view, me.srcOperand.view);
		  }
		} else if (me.srcOperand.type == "Viewset") {
		  me.app.onComposeView(tgt.view, me.srcOperand.data);
		}
	  } else if (tgt.type == "Viewset") {
		// src better not be viewset!
		me.app.onComposeView(tgt.data, me.srcOperand.data);
	  } else if (tgt.type == "Create") {
        console.group("Iact.onDrop Create new view");
        console.log(me.srcOperand.data.q.toSql().toString());
        console.groupEnd();
        me.app.onCreateView(me.srcOperand.data);
	  }
	}

	e.stopPropagation();
	me.srcOperand = null;
  };

  return me;
});




let SelectionHandler = (function selectionHandler({boxid, viewManager}){
  let start = null;
  let end = null;

  function me() { }
  me.type = "selectionHandler";
  me.dom = $(`#${boxid}`);
  me.onStartHandler = () => {};
  me.isDisabled = false;
  me.onStart = (cb) => {
	if (cb) me.onStartHandler = cb;
  };
  me.disable = () => {
    me.isDisabled = true;
    me.reset();
	viewManager.selectViews(null);
  };
  me.enable = () => {
    me.isDisabled = false;
  };


  me.onDown = (e) => { 
    if (me.isDisabled) return;
    if (descendantOfClass(e.target, "holder")){
      start = null;
      viewManager.dom[0].releasePointerCapture(e.pointerId);
      return;
    }
	me.onStartHandler(me);
    start = end = { x: e.pageX, y: e.pageY };
    viewManager.dom[0].setPointerCapture(e.pointerId);
  };
  me.onMove = (e) => { 
    if (me.isDisabled) return;
    if (!start) return;
    if (e.buttons != 1) {
      start = null;
      return;
    }
    end = { x: e.pageX, y: e.pageY };
    me.render();
  };

  me.onUp = (e) => { 
    if (me.isDisabled) return;
    if (!start) {
	  end = null;
	  me.render();
	  return;
	}
    end = { x: e.pageX, y: e.pageY };
    if (end.x == start.x && end.y == start.y) {
      start = end = null;
      me.render();
    } else {
      me.render();
      // rendering before setting start to null makes sure we preserve
      // the selection box
      start = null;
    }
    viewManager.dom[0].releasePointerCapture(e.pointerId);
  };

  me.getBBox = () => {
    return {
      l: Math.min(start.x, end.x), // left
      t: Math.min(start.y, end.y), // top
      w: Math.abs(start.x - end.x),
      h: Math.abs(start.y - end.y)
    }
  };

  me.render = () => {
    if (!start || !end) {
      me.reset();
	  viewManager.selectViews(null);
      return;
    }
    let bbox = me.getBBox();
	let viewOffset = $("#views").offset();
	bbox.l -= viewOffset.left;
	bbox.t -= viewOffset.top;
    let css = {
      display: "block",
      left: `${bbox.l}px`,
      top: `${bbox.t}px`,
      width: `${bbox.w}px`,
      height: `${bbox.h}px`
    };
    me.dom.css(css);

    viewManager.selectViews(bbox);
  };

  me.reset = () => {
	start = end = null;
    me.dom.css({ display: "none" });
  };

  return me;
});



let ViewSetDropzone = ((viewManager) => {
  let me = () => {};
  me.viewManager = viewManager;
  me.dom = $("#viewsetdrop");
  me.views = [];

  me.setViews = (views) => {
	me.views = views || [];
	me.render();
  };

  me.render = () => {
	me.dom.empty();

	me.views.forEach((view) => {
	  let el = $(`<div>${view.viewName}</div>`);
	  me.dom.append(el);
	});

	return me;
  };

  const handler = me.viewManager.composeHandler;
  me.dom[0].addEventListener("pointerdown", (e) => {
	if (!me.views || !me.views.length) return
	handler.onStart(e, {
	  type: "Viewset",
	  data: me.views,
	  dom: me.dom
	}, me.dom.clone());
  });

  me.dom[0].addEventListener("pointerup", (e) => {
	handler.onDrop(e, {
	  type: "Viewset",
	  data: me.views,
	  dom: me.dom
	});
  });

  me.dom[0].addEventListener("pointermove", (e) => {
	handler.onMove(e, {
	  type: "Viewset",
	  data: me.views,
	  dom: me.dom
	});
  });


  return me;
});

let NewViewDropzone = ((viewManager) => {
  let me = () => {};
  me.viewManager = viewManager;
  me.dom = $("#newviewdrop");
  me.view = null;


  const handler = me.viewManager.composeHandler;
  me.dom[0].addEventListener("pointerup", (e) => {
	handler.onDrop(e, {
	  type: "Create",
	  dom: me.dom
	});
  });

  me.dom[0].addEventListener("pointermove", (e) => {
	handler.onMove(e, {
	  type: "Create",
	  dom: me.dom
	});
  });



  return me;
});

function Views({app}) {
  const db = app.db;
  const containerid = app.containerid;
  const viewsDomEl = $$1("#views");
  let viewid = 0;

  function me() {}
  me.app = app;
  me.dom = $$1(`#${containerid}`);
  me.views = [];
  me.selectedViews = [];
  me.composeHandler = ComposeHandler(me);
  me.selectionHandler = SelectionHandler({ boxid: "selbox", viewManager: me });
  me.viewsetDropzone = ViewSetDropzone(me);
  me.newViewDropzone = NewViewDropzone(me);

  me.newViewId = (prefix="V") => `${prefix}${viewid++}`;

  me.render = () => {
    me.views.forEach(async (v) => {
      // need to add v.dom to DOM before vega-lite can render a chart
      //me.dom.append(v.dom);
      await v.render(db);
    });
    return me;
  };

  me.enable = () => {
    $$1(".table-handle").addClass("enabled");
    me.selectionHandler.enable();
    me.views.forEach(async (v) => {
      v.setCompositionMode(true);
    });
    me.render();
  };

  me.disable = () => {
    $$1(".table-handle").removeClass("enabled");
    me.selectionHandler.disable();
    me.views.forEach((v) => {
      v.setCompositionMode(false);
    });
    me.render();
  };


  /*
  * given the mapping defined by user interactions, construct 
  * the Query object.  Make some "sensible" decisions about how
  * to construct the query
  *
  * @table: String base table/view name
  * @mapping: { vis attr: Attr object }
  *
  * @return: Query plan
  */
  function toQuery(table, mapping) {
    const gbattrs = R$1.values(R$1.pick(["x", "color", "shape"], mapping));
    let Agb = gbattrs.map((attr) => PClause({e:attr, alias: attr.attr }));
    let y = null;
    if (mapping.y){
      y = PClause({e:Func({fname:"avg", args:[mapping.y]}), alias: mapping.y.attr});
    } else {
      y = PClause({e:VCA.parse("count(1)"), alias: "count"});
    }
    mapping.measure = y.alias;


    return GroupBy({ 
      Agb, 
      Fs: [y], 
      child: Source({ source: table })
    })

  }


  // Creates new View objects given output of encoding shelf
  //
  // @table: String base table/view name
  // @mapping: { vis attr: Attr object }
  // @mark: String mark type
  // @name: optional view name
  //
  // @return: Array of View objects.  
  me.createViews = async (table, mapping, mark, name) => {
    const Q = toQuery(table, mapping);
    const r = R$1.map((attr) => { return attr.attr }, mapping);
    r.mark = mark;
    r.measure = Q.Fs[0].alias;

    let V = View({ q: Q, r, name });
    if (mapping.facet) {
      delete V.mapping.facet;
      let Vs = me.facetView(V, mapping.facet.attr, name);
      await me.addViews(Vs);
    } else {
      await me.addView(V);
    }
  };

  me.facetView = async (view, facetAttr) => {
    const buckets = await getFacetBuckets(me.app.db, view.q, facetAttr);
    let views = [];
    for (let {where, facet, val} of buckets) {
      let fq = Where({ exprs: where, child: view.q.clone()});
      views.push(View({
        q: fq,
        r: R$1.clone(view.mapping),
        name: `${view.viewName} (${facet}=${val})`
      }));
    }
    return views;
  };


  me.addView = async (view) => {
    await me.addViews([view]);
    return me;
  };

  me.addViews = async (views) => {
    if (!R$1.is(Array, views))
      views = [views];

    for (let v of views) {
      try {
        if (!v.id) 
          v.id = me.newViewId();
        if (!v.viewName) 
          v.viewName = v.id;

        v.setViewManager(me);
        me.views.push(v);

        if (v.init)
          v.init(db);
        me.dom.append(v.dom);
        await v.render(db);

      } catch (e) {
        me.onRemoveHandler(v);
        console.error(v);
        throw e;
      }
    }

    return me;
  };

  me.onRemoveHandler = (v) => {
    // remove from views
    const idx = me.views.indexOf(v);
    if (idx > -1) {
      me.views.splice(idx, 1);
      v.dom[0].remove(); // remove view's dom directly, no need to rerender
    } else {
      debug(`ERR: Couldn't find view ${v.id} to remove`);
    }
  };

  me.clear = (v) => {
    me.views.forEach((v) => v.dom[0].remove());
    me.views = [];
  };


  function getViewBBox(v) {
    let viewOffset = viewsDomEl.offset();
    let {top, left} = v.vldiv.offset();
    top -= viewOffset.top;
    left -= viewOffset.left;
    return {
      t: top, l: left, w: v.vldiv.width(), h: v.vldiv.height()
    }
  }

  // TODO: SPLIT this into multiple methods
  // 1. update selected interface
  // 2. update viewset dropzone
  // 3. update contextmenu (don't render if dropzone used to start drag)
  //
  // @displayOnly: falsy to update me.selectedViews.  true to only update display
  me.selectViews = (bbox, displayOnly) => {
	let selectedViews = [];
    me.views.forEach((v) => {
      if (!v.holder) return;
      v.holder.removeClass("selected");
      if (bbox && bboxOverlap(bbox, getViewBBox(v))) {
        v.holder.addClass("selected");
        selectedViews.push(v);
      }
    });
	if (!displayOnly) {
	  me.selectedViews = selectedViews;

	  if (bbox)
		me.viewsetDropzone.setViews(me.selectedViews);
	  if (me.selectedViews.length > 0 && me.app.onViewsSelected)
		me.app.onViewsSelected(me.selectedViews);
	}

  };



  //
  //
  // Logic to manage composition interactions and the display updates
  // 1. views construct the source and target data in the format:
  // {
  // 	type: "View" | "Mark" | "Viewset" | "Create"
  // 	data: the View object(s) of the actual operand
  // 	svg:  for Mark operands, the SVG dom element
  // 	view: the originating View object for the event
  // }
  // 2. during an interaction, update the displays
  //
  //
  me.dom[0].addEventListener("pointerdown", me.onStartViews);
  me.dom[0].addEventListener("pointermove", me.onMoveViews, true);
  me.dom[0].addEventListener("pointerup", me.onDropViews, true);

  me.onStartViews = (e) => {
	if (!me.isCompositionMode()) return;
	if (!me.composeHandler.srcOperand) return;
	me.dom[0].setPointerCapture(e.pointerId);
  };

  // onMove handler for #views container
  me.onMoveViews = (e) => {
	me.composeHandler.onMove(e, null);
  };

  me.onDropViews = (e) => {
	if (e.target == me.dom[0]) {
	  console.log("Views.onDropViews target:", e.target);
	  me.composeHandler.onDrop(e, null);
	} 
  };




  // finally, register handlers
  me.dom[0].addEventListener("pointerdown", (e) => {me.selectionHandler.onDown(e);});
  me.dom[0].addEventListener("pointermove", (e) => {me.selectionHandler.onMove(e);});
  me.dom[0].addEventListener("pointerup", (e) => {me.selectionHandler.onUp(e);});
  //me.dom[0].addEventListener("dragend", (e) => me.composeHandler(e, "end", me))

  return me;
}

let DummyViewManager = (({slider, viewManager}) => {
  let me = () => {};
  me.viewManager = viewManager;
  me.slider = slider;
  me.app = viewManager.app;

  me.addView = me.viewManager.addView;
  me.onMoveViews = me.viewManager.onMoveViews;
  me.onLiftView = me.viewManager.onLiftView;
  me.composeHandler = me.viewManager.composeHandler;

  me.onRemoveHandler = (view) => {
    viewManager.onRemoveHandler(slider);
  };

  return me;
});


let Slider = (({ q, view, sliderAttr, opts }) => {
  let me = () => {};
  me.dom = $("<div class='slider'/>");
  me.q = q; // base query, canonical form
  me.view = view;
  me.viewManager = null;
  me.min = opts.min || 0;
  me.max = opts.max || 100;
  me.value = opts.value || me.min;
  me.step = opts.step || (me.max - me.min) / 10;
  me.width = opts.width || 200;
  me.sliderAttr = sliderAttr;
  me.slider = null;
  me.label = null;

  me.setViewManager = (viewManager) => {
    me.viewManager = viewManager;
    me.view.setViewManager(DummyViewManager({slider: me, viewManager}));
  };

  me.setInteractionMode = (mode) => 
    me.view.setInteractionMode(mode);

  me.init = () => {
    if (me.view) {
      if (!me.view.id)
        me.view.id = me.viewManager.newViewId();
      me.view.width = me.width;
      me.view.setViewManager(DummyViewManager({
        slider: me, 
        viewManager:me.viewManager
      }));
      if (me.view.init) {
        me.view.init(me.viewManager.app.db);
      }
    }

    me.label = $("<span class='label'/>");
    me.label.text(`${me.sliderAttr.attr}: ${me.value}`);
    me.slider = $(`<input type="range" 
      class="" min="${me.min}" max="${me.max}"
      value="${me.value}" step="${me.step}"
      style="width:${me.width-75}px" >`);
    me.slider.on("input", me.onChange);
    me.slider_container = $("<div/>");
    me.slider_container
      .append(me.label)
      .append(me.slider);

    me.dom.append(me.view.dom);
    me.dom.append(me.slider_container);

    return me
  };

  me.render = async () => {
    //me.dom.empty()

    await me.view.render();
    me.slider.off("input").on("input", me.onChange);

    return me
  };

  me.onChange = async (e) => {
    if (!me.slider) return;
    e.stopPropagation();

    let val = +me.slider.val();
    let newQ = me.q.clone();
    let a = me.sliderAttr;
    let where = Where({exprs:[
      Expr({op:">=", l:a, r:Value({value:val-me.step})}),
      Expr({op:"<", l:a, r:Value({value:val+me.step})})
    ] });
    where.c = newQ.c;
    newQ.c = where;
    
    me.label.text(val);

    // update chart
    me.view.updateQuery(newQ);
    await me.view.render();
  };

  return me;
});

async function App({db,  containerid}){

  function me() {}
  me.db = db;
  me.containerid = containerid;
  me.viewCreateHandler = ViewCreateHandler();

  me.VCA = VCA({app:me});
  me.viewManager = Views({ app: me });
  me.contextMenu = ContextMenu({ containerid: "contextmenu-container", app: me });





  //
  // Logic to manage algebra interactions
  //

  me.onViewsSelected = (views) => {
    me.contextMenu.state = R$1.isEmpty(views)? null : "nary";
    me.contextMenu.render();
    me.v1 = me.v2 = null;
  };

  me.onComposeView = (v1, v2) => {
    me.contextMenu.state = (v1 && v2)? "binary" : null;
    me.contextMenu.render();
    me.v1 = v1;
    me.v2 = v2;
  };

  me.onLiftView = (v) => {
    me.v2 = null;
    me.v1 = v;
    me.contextMenu.state = (v)? "lift" : null;
    me.contextMenu.render({v});
  };

  me.onNaryOp = async (op) => {
    let views = me.viewManager.selectedViews;
    if (R$1.isEmpty(views)) return;

    let operation = me.VCA.dot;
    if (op.type == "stats") 
      operation = me.VCA.dot;
    else if (op.type == "union") 
      operation = me.VCA.union;
    else
      return

    try {
      let v3 = await operation(op, views);
      await me.viewManager.addView(v3);
    } catch (e) {
      debug(e);
    }

    me.contextMenu.close();
  };

  me.onCreateView = async (v) => {
    await me.viewManager.addView(v);
  };


  me.onBinaryOp = async (op) => {
    // check that source and target views/viewsets are actually set
    if (me.v1 && me.v2) {
      let operation = null;
      if (op.type == "stats") 
        operation = me.VCA.dot;
      else if (op.type == "union") 
        operation = me.VCA.union;
      else
        console.log(`Binary op type ${op.type} not recognized`);

      try {
        let v3 = await operation(op, me.v1, me.v2);
        await me.viewManager.addViews(v3);
      } catch (e) {
        debug(e);
      }

      me.contextMenu.close();
    }
  };

  me.onLift = async (op) => {
    if (me.v1) {
      try {
        let v2 = await me.VCA.lift(op, me.v1);
        await me.viewManager.addViews(v2);
      } catch (e) {
        debug(e);
      }
    }
    me.contextMenu.close();
  };

  // pressing enter chooses defaults if context menue is active
  document.body.addEventListener("keydown", (e) => {
    if (e.key == "Enter" || e.key == "u" || e.key == "+" || e.key == "-") {
      me.contextMenu.onHotKey(e.key);
    } else if (e.key == "t") {
      me.toggleInteractionMode();
    }
  });


  //
  // initialize toggle for interaction vs composition modes
  // 
  me.toggleModeBtn = $("#toggle-mode");
  me.toggleModeBtn.on("click", () => me.toggleInteractionMode());
  me.interactionMode = "interaction"; // or "composition"
  me.isCompositionMode = () => me.interactionMode == "composition";
  me.toggleInteractionMode = () => {
    me.interactionMode = (me.isCompositionMode())? "interaction":"composition";
    me.updateInteractionMode();
  };


  me.updateInteractionMode = () => {
    if (me.isCompositionMode()) {
      me.toggleModeBtn.text("Composition Mode");
      $("#navbar").addClass("composition");
      me.viewManager.enable();
    } else {
      me.toggleModeBtn.text("Interaction Mode");
      $("#navbar").removeClass("composition");
      me.viewManager.disable();
    } 
  };
  me.updateInteractionMode();

  return me;
}

async function loadSlider(app) {
  let viewManager = app.viewManager;
  viewManager.clear();

  let v = View({
    q: VCA.parse("SELECT cyl, avg(mpg) as mpg FROM cars "),
    r: { x: "cyl", y: "mpg", measure: "mpg"  },
    name: "all",
    opts: {
      height: 300
    }
  });

 v = View({
    q: VCA.parse(`select state, percdem as count from electionrd where party = \"DEMOCRAT\"`),
    r: { mark: "map", measure: "count"},
    name: "Election Statistics",
    opts: {
      width: 400,
      height: 300
    }
  });
 
  //viewManager.addView(v)
  await viewManager.addView(Slider({
    q: v.q,
    view: v,
    sliderAttr: Attr('year'),
    opts: {
      min: 1976, max: 2020, step: 4,
      width: 600
    }
  }));
  return app;
}
async function loadElection(app) {
  let viewManager = app.viewManager;
  let years = [ 2008, 2012, 2016, 2020];
  for (let year of years) {
   let map = View({
      q: VCA.parse(`select state, percdem as count from electionrd where year = ${year} and party = \"DEMOCRAT\"`),
      r: { mark: "map", measure: "count"},
      name: year,
      opts: {
        width: 400,
        height: 300
      }
    });
    await viewManager.addView(map);
  }

  //await viewManager.addView(View({
  //  q: VCA.parse("select year, avg(percdem) as avg from electionrd where year >= 2008"),
  //  r: { mark: "table", measure: "avg", avg: "avg"},
  //  name: "Nationide Domcratic Percentage"
  //}))
  return app;
}

async function loadMusicBasic(app) {
  let viewManager = app.viewManager;
  let boros = ['Vinyl Single', 'Cassette'];//, 'CD']
  let views = boros.map((boro) => 
    View({
      q: VCA.parse(`SELECT year, avg(revenue) as revenue FROM music WHERE format = '${boro}'`),
      r: { x: "year", y: 'revenue', measure: "revenue", mark: "bar" },
      name: `${boro} revenue`,
      opts: {
        width: 600, height: 250
      }
    }));
  await viewManager.addViews(views);
}


async function loadCarsNary(app) {
  let viewManager = app.viewManager;
  let carbs = [1,2,3,4,6,8];
  let views = carbs.map((carb) => 
    View({
      q: VCA.parse(`SELECT cyl, avg(mpg) as mpg FROM cars WHERE carb = ${carb}`),
      r: { x: "cyl", y: 'mpg', measure: "mpg", mark: "bar" },
      name: `carb=${carb}`,
      opts: {
        width: 300, height: 250
      }
    })
  );
  await viewManager.addViews(views);
}


async function loadCarsLift(app) {
  let viewManager = app.viewManager;
  let carbs = [1,2,4];
  let views = carbs.map((carb) => 
    View({
      q: VCA.parse(`SELECT cyl, avg(mpg) as mpg FROM cars WHERE carb = ${carb}`),
      r: { x: "cyl", y: 'mpg', measure: "mpg", mark: "bar" },
      name: `carb=${carb}`,
      opts: {
        width: 300, height: 250
      }
    })
  );
  await viewManager.addViews(views);
}





async function loadSPEncoding(app) {
  let viewManager = app.viewManager;
  let tickers = ['BAC', 'AXP', 'COF'];
  let names = ["Bank of America", "American Express", "Capital One"];
  let views = R$1.zip(tickers, names).map(([symb, name]) => 
    View({
      q: VCA.parse(`select day, high from sp100 where name = '${symb}'`),
      r: { x: "day", y: 'high', measure: "high", mark: "point" },
      name: `${name} daily price`,
      opts: {
        width: 400,
        height: 200
      }
    }));

  views.push(
    View({
      q: VCA.parse("SELECT day, avg(high) as high FROM sp100 where day > 120 "),
      r: { mark: "table",  day: "day", high: "high", measure: "high" },
      name: "Recent Average Prices"
    })
  );
  //views.push(
  //  View({
  //    q: VCA.parse("SELECT volume, open, avg(high) as high from sp100 where name = 'MSFT'"),
  //    r: { x: "volume", y: "open", color: "high", measure: "high", mark: "point"},
  //    name: "Microsoft volume vs open"
  //  })
  //)
  await viewManager.addViews(views);
}

async function loadCarsEncoding(app) {
  let viewManager = app.viewManager;
  let views = [
    View({
      q: VCA.parse("SELECT cyl, avg(mpg) as mpg FROM cars WHERE am = 1"),
      r: { x: "cyl", y: 'mpg', measure: "mpg" },
      name: "am=1"
    }),

    View({
      q: VCA.parse("SELECT cyl, hp, avg(mpg) as mpg FROM cars "),
      r: { mark: "point",  x: "cyl", color: "mpg", y: "hp", measure: "mpg" },
      name: "all"
    }),
    View({
      q: VCA.parse("select cyl, mpg  from cars where hp < 100"),
      r: { mark: "table", y: "mpg", cyl: "cyl", measure: 'mpg' },
      name: "low hp",
    })
  ];
  await viewManager.addViews(views);
}



const demos = [
  {
    name: "--",
    description: `<div>
     <h3>VCA Demonstration</h3>
    <p>This website contains demo applications to illustrate the expressiveness
    of a view composition algebra.   Use the above dropdown to select 
    <p>Click here for the accompanying paper. </p>
    </div> `
  },
  {
    name: "Binary Composition",
    description: `<div>
    <h3>Basic Composition</h3>
    <p>
      These examples will guide you in using VCA's view composition interactions.
    The charts visualize annual music sales revenue for vinyl and cassette music formats. 
    At what point did cassette sales exceed vinyl sales?  
    The charts have different y-axis scales, so it is hard to compare. 
    </p>
    <p>
      To start, click "Interaction Mode" in the title bar, or press 't' to enter "Composition Mode" (the title bar should turn blue when you are in composition mode). 
Drag the title bar for the vinyl chart over the cassette chart.  
    This will show a context menu on the right side, with the composition operator "-" already highlighted.  Click the button or press <code>enter</code> to compose the charts</p>
  <p>
  Now try dragging the right chart onto the left, or choosing different binary stats operations, such as "+", "min", or "max".     You can also drag an individual mark to any title bar!
  </p>
  <p>
  Finally, you can select the "Union" operation as well, which will juxtapose (for bar charts) or superpose the marks into a single view.  Since there are many years, juxtaposing the marks will create a very wide chart!
  </p>
    </div>`,
    f: loadMusicBasic
  },
  {
    name: "Nary Composition",
    description: `<div>
    <h3>Union Composition</h3>
    <p>
      This example illustrates VCA's nary operators. 
      Each chart shows average MPG by cylinder for cars with different numbers of carburetors.
      Notice that for some numbers of carburetors, cars tend to have different numbers of cylinders.
    </p>
    <p>
    How many cars containing 1, 2, or 3 carburetors are there in the dataset per cylinder?  
  Drag a selection box in the space below (start the drag
    in an empty space and not on a chart) to select the first three charts.     The context menu on the right lists different aggregation functions for statistical composition, as well as the option to union the marks together.  
  To answer the above question, click on <code>count</code>.
    </p>
    <p>
  When you select a set of views, the <b>Selected Viewset</b>
  box on the left will list the views that you have selected.  
VCA lets you compose individual charts with viewsets as well.
  For instance, try selecting <code>carb=2</code> and <code>carb=3</code> and comparing the viewset with <code>carb=1</code>.  
    </p>
    </div>`,
    f: loadCarsNary
  },
  {
  name: "VCA and Models",
  description: `<div>
  <h3>Lifting Views into Models</h3>
  <p>
  This example illustrates how to lift a view into a model to better
facilitate view comparisons.
  Notice that <code>carb=2</code> only contains data for 4 and 8 cylinder cars, while <code>carb=4</code> only contains 6 and 8 cylinder cars.  Thus, if we compare the two charts, only the 8 cylinder statistics will be compared.  
  </p>
  <p>
  Lifting the view lets us compare <code>carb=4</code> with the <i>expected</i> MPG statistics in <code>carb=2</code>, assuming that there is a linear relationship between cylinders and MPG.  To do so, click on <img src="./static/images/trending_up_black_24dp.svg"/> in the title bar of <code>carb=2</code>.  </p>
  <p>The context menu lists three models, and lets you pick which grouping attributes should be used as features to fit the model, or conditioning variables for which a separate model is fit for each unique value.  Simply press <b>enter</b> to create the model view.  You can now drag <code>carb=4</code> onto the model view to compare the two charts.
  </p>
  </div>`,
  f: loadCarsLift

  },
  {
    name: "Cross Encoding Composition",
    description: `<div>
    <h3>Cross Encoding Composition</h3>
    <p>
      This example shows how VCA helps users compare across different visual encodings.  The three charts show 100 days of stock prices for Bank of America, American Express, and Capital One, and the table shows the average stock prices over the recent 3 days.
    </p>
    <p>
    A basic question is how each stock compares with the average price in day 124.   Drag the desired table cell onto a chart (or a view set of all three charts) to perform the comparison.  The output renders the difference between the company's daily stock price and the overall average.
    </p>
    </div>`,
    f: loadSPEncoding
  },
  {
    name: "Third-Party Map Composition",
    description: `<div>
    <h3>Third-party Map Composition</h3>
    <p>
    This example is an illustration of adapting a third-party visualization library (<a href="https://leafletjs.com/">LeafletJs</a>) to support VCA.  Each map renders per state Democrat-Republican voting percentages for a given presidential election year.
  Because VCA performs transformations at the data level, third party visualizations can be integrated by writing a simple wrapper.
    </p>
  <p>How did voting percentages change between 2008 and each of the other three elections?   Do answer this, select the 2012-2020 maps to create a view set, and then drag 2008 onto the <b>Selected Viewset</b> box.
  </p>
    </div>`,
    f: loadElection
  },
  {

    name: `VCA + Interaction`,
    description: `<div>
      <h3>VCA and Slider Interaction</h3>
      <p>
      This example illustrates how you can save and compose different states of an interactive view.
      The chart renders US presidentia election statistics from 1976 to 2020 with the help of the interactive slider.  
      </p>
      <p>
      The current chart can be saved by dragging the title of the chart onto
the <b>Create View Dropzone</b>.  In bar charts and scatterplots you can also select marks in the chart
and press the <img src="./static/images/open_in_new_black_24dp.svg"/> button in the title bar to create a new view.  
      You can now compare the slider's chart with the saved one.
      </p>
    </div>`,
    f: loadSlider
  }
];

let loadDemo = (app) => {
  let dom = $("<div class='nav-item nav-link active demo'/>");
  let ul = $("<select/>");
  dom.append($("<span>Demos</span>"));
  dom.append(ul);

  let onChange = () => {
    let {name, description, f} = R$1.filter(({name}) => name == ul.val(), demos)[0];
    $("#demo-description").empty()
      .append($(description))
      .css({display: "block"});
    app.viewManager.clear();
    if (f) f(app);
  };

  demos.forEach(({ name, description, f}) => {
    let option = $(`<option value='${name}'>${name}</option>`);
    ul.append(option);
  });

  ul.on("change", onChange);
  onChange();

  $("#navbar .navbar-nav").append(dom);
  return app;
};

Object.defineProperty(exports, 'initSqlJs', {
enumerable: true,
get: function () {
return sql_js.initSqlJs;
}
});
exports.App = App;
exports.Attr = Attr;
exports.Expr = Expr;
exports.Func = Func;
exports.GroupBy = GroupBy;
exports.Join = Join;
exports.PClause = PClause;
exports.Paren = Paren;
exports.Project = Project;
exports.RemoteDB = RemoteDB;
exports.Source = Source;
exports.Union = Union;
exports.VCA = VCA;
exports.Value = Value;
exports.View = View;
exports.Views = Views;
exports.Where = Where;
exports.loadCarsEncoding = loadCarsEncoding;
exports.loadCarsLift = loadCarsLift;
exports.loadCarsNary = loadCarsNary;
exports.loadDemo = loadDemo;
exports.loadElection = loadElection;
exports.loadMusicBasic = loadMusicBasic;
exports.loadSPEncoding = loadSPEncoding;
exports.loadSlider = loadSlider;
exports.loadSqliteDB = loadSqliteDB;
exports.parse = parse;
exports.sql = query;

Object.defineProperty(exports, '__esModule', { value: true });

})));
