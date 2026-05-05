## Syntax

Basic syntax trees are just expressions:

exp := var
    |  op
    |  (op exp)
    |  (exp op)
    |  exp `exp` exp
    |  exp op exp  // operator precedence
    |  const      // integers, floats, strings
    |  Con
    |  exp exp    // application (left assoc)
    |  exp : exp  // ascription (slightly tighter than =)
    |  { defs }   // block / record
    |  ( exp )    // parens
    |  ( exp (, exp)* ) // tuples
    |  [] | [ exp (, exp)* ]  // vecs
    |  fn exp { defs }  // no curlies in exp
    |  _                // wildcard
    |  case exp { defs }
    |  do exp <- exp { defs } // exp2 (fn exp1 { defs })?
    |  exp := exp  // mutable?
    |  exp.exp     // indexing
    |  if exp then exp else exp
    |  if exp <- exp then exp else exp

defs := empty
     |  def
     |  def ; defs  // Here ; can be newline

def :=  exp = exp
    |   infix[lr] op
    |   exp = data { defs }
    |   exp = type exp
    |   exp = struct { defs }
    |   exp <- exp ; defs  // Here ; can be newline, means fn exp1 { defs } exp2.  Or does it?
    |   fun exp { defs }    // Named function, one disjunct.
    |   exp   // final or void exp.

top := export { exp } imports
    |  imports

imports := import exp { exp } ; imports
        |  defs

