inductive Pair : Type
| nil : Pair
| str (s: String) : Pair
| cons (car: Pair) (cdr: Pair) : Pair
deriving DecidableEq

instance : Repr Pair := ⟨
  λp n =>
    let rec pairToFormat p :=
      match p with
      | Pair.nil => Std.Format.nil
      | Pair.str s => Std.Format.bracket "\"" s "\""
      | Pair.cons car cdr =>
        let carlist := pairToFormat car |> if let Pair.str s := car then id else Std.Format.paren;
        let cdrlist := pairToFormat cdr;
        let sep := if let Pair.str s := cdr then " . " else " ";
        carlist ++ sep ++ cdrlist
    pairToFormat p |> Std.Format.paren
⟩

declare_syntax_cat pair
syntax ident : pair
syntax "(" pair* ("." pair)? ")" : pair
syntax "fromLisp%" pair : term

def aux (s: List Lean.Syntax) (t: Option Lean.Syntax) : Lean.MacroM Lean.Syntax := do
match s with
| [] => if let some t' := t then `($t') else `(Pair.nil)
| x :: xs => `(Pair.cons $x $(←aux xs t))

macro_rules
| `(fromLisp% $p) => `($p)
| `(pair| $e:ident) => `(Pair.str $(Lean.quote e.getId.toString))
| `(pair| ($e*)) => aux e.data none
| `(pair| ($e1* . $e2)) => aux e1.data (some e2)

#eval Pair.cons (Pair.str "a") (Pair.cons (Pair.cons (Pair.str "b") (Pair.str "c")) (Pair.cons Pair.nil Pair.nil))
#eval fromLisp% (lambda (b c) d q w e r t y u . e)