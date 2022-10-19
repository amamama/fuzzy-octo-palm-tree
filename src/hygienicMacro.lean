inductive Pair {T: Type} : Type
| nil : Pair
| atom (s: T) : Pair
| cons (car: @Pair T) (cdr: @Pair T) : Pair
deriving DecidableEq, Inhabited

instance [Repr T] : Repr (@Pair T) := ⟨
  λp n =>
    let rec pairToFormat p :=
      match p with
      | Pair.nil => Std.Format.nil
      | Pair.atom s => repr s
      | Pair.cons car cdr =>
        let carlist := pairToFormat car |> if let Pair.atom _ := car then id else Std.Format.paren;
        let cdrlist := pairToFormat cdr;
        let sep := if let Pair.atom s := cdr then " . " else " ";
        carlist ++ sep ++ cdrlist;
    "fromLisp%" ++ (pairToFormat p |> if let Pair.atom _ := p then id else Std.Format.paren)
⟩

declare_syntax_cat pair
syntax ident : pair
syntax str : pair
syntax num : pair
syntax "(" pair* ("." pair)? ")" : pair
syntax "fromLisp%" pair : term

def aux (s: List Lean.Syntax) (t: Option Lean.Syntax) : Lean.MacroM Lean.Syntax := do
match s with
| [] => if let some t' := t then `($t') else `(Pair.nil)
| x :: xs => `(Pair.cons $x $(←aux xs t))

macro_rules
| `(fromLisp% $p) => `($p)
| `(pair| $e:ident) => `(Pair.atom $(Lean.quote e.getId.toString))
| `(pair| $e:strLit) => `(Pair.atom $e)
| `(pair| $e:numLit) => `(Pair.atom $(Lean.quote e.toNat.repr))
| `(pair| ($e*)) => aux e.data none
| `(pair| ($e1* . $e2)) => aux e1.data (some e2)

#eval Pair.cons (Pair.atom "a") (Pair.cons (Pair.cons (Pair.atom "b") (Pair.atom "c")) (Pair.cons Pair.nil Pair.nil))
#eval fromLisp% (lambda (b c) d q 1 w e "po" r t y u . e)

mutual
  inductive SynEnv {S T: Type}: Nat → Type
  | nil : SynEnv 0
  | cons {n: Nat} (ents: List (@Entry S T)) (cdr: @SynEnv S T n) : SynEnv (n + 1)
  inductive Name {S T: Type} : Type
  | ident {n: Nat} (name: S) (env: @SynEnv S T n) (mark: List Nat) : Name
  | lit (lit: S) : Name
  inductive Entry {S T: Type} : Type
  | rename (name: S) (mark: List Nat) (new_name: T) : Entry
  | keyword (name: S) : Entry
  | syn (name: S) (mark: List Nat) (definition: @Pair (@Name S T)) : Entry
end

instance [Repr S] [Repr T] : Repr (@Name S T) where
reprPrec
  | Name.ident name env mark, n =>
  let aux {n: Nat} (env: @SynEnv S T n) := "E" ++ (repr n);
    Std.Format.joinSep [(repr name), (aux env), (repr mark)] ":"
  | Name.lit lit, n => (repr lit)

instance [Repr S] [Repr T] : Repr (@Entry S T) where
reprPrec
  | Entry.rename name mark orig_name, n => Std.Format.joinSep [(repr name), (repr mark), "rename", (repr orig_name)] ":"
  | Entry.keyword name, n => Std.Format.joinSep [(repr name), "keyword"] ":"
  | Entry.syn name mark definition, n => Std.Format.joinSep [(repr name), (repr mark), "<proc>"] ":"

instance {n: Nat} [Repr S] [Repr T] : Repr (@SynEnv S T n) := ⟨
  λenv _ =>
    let rec envToFormat {n} e :=
    match e with
    | SynEnv.nil => Std.Format.nil
    | SynEnv.cons ent e => "E" ++ (repr n) ++ ":" ++ (repr ent) ++ Std.Format.line ++ envToFormat e
    envToFormat env
⟩

abbrev Ident := String × Nat
abbrev Atom := @Name String Ident

def init_for_macro_expansion {S T: Type} (init_env: @SynEnv S T 1): @Pair S → @Pair (@Name S T)
| Pair.nil => Pair.nil
| Pair.cons car cdr => Pair.cons (init_for_macro_expansion init_env car) (init_for_macro_expansion init_env cdr)
| Pair.atom s => Pair.atom (Name.ident s init_env [1])

structure Setting {T: Type} where
  s_lambda : T
  s_if : T
  s_quote : T
  s_letrec : T
  s_letrec_syntax : T

def Setting.is_keyword {T: Type} [DecidableEq T] (t: T) (s: @Setting T) :=
  s.s_lambda = t ∨ s.s_if = t ∨ s.s_quote = t ∨ s.s_letrec = t ∨ s.s_letrec_syntax = t

instance [DecidableEq T] : Decidable (Setting.is_keyword t (s: @Setting T)) :=
  inferInstanceAs (Decidable (_ = _ ∨ _ = _ ∨ _ = _ ∨ _ = _ ∨ _ = _))

def Setting.initial_syntax_environment {S T: Type} (s: @Setting S) :=
  let keywords: List (@Entry S T) := [
    Entry.keyword s.s_lambda,
    Entry.keyword s.s_if,
    Entry.keyword s.s_quote,
    Entry.keyword s.s_letrec,

    Entry.keyword s.s_letrec_syntax
  ];
  (SynEnv.cons keywords SynEnv.nil)

def setting_String := {
  s_lambda := "lambda"
  s_if := "lambda"
  s_quote := "lambda"
  s_letrec := "lambda"
  s_letrec_syntax := "lambda"
  : Setting
}

#eval (setting_String.initial_syntax_environment:@SynEnv String Ident _)

def test1 := fromLisp% (lambda (b c) d q w e r t y u . e)
#eval test1

def test2 := @init_for_macro_expansion String Ident setting_String.initial_syntax_environment test1
#eval test2
def test3 :=
  (if let Pair.cons car cdr := test2 then car else test2)
  |> λp => if let Pair.atom s := p then s else @Name.lit String Ident "0"
#eval test3


def Name.lookup {S T: Type} [DecidableEq S] (name: @Name S T) : Option (@Entry S T) :=
match name with
| Name.lit _ => none
| Name.ident name env mark =>
  let rec lookup_aux {gen: Nat} (env: @SynEnv S T gen) (mark: List Nat) :=
  match gen, env, mark with
  | _, SynEnv.nil, _ => none
  | _, _, [] => none
  | n + 1, SynEnv.cons ents env, mark@(m :: ms) =>
    let mark := if m > gen then ms else mark;
    let rec lookup_entry (ents: List Entry) :=
    match ents with
    | [] => none--lookup_aux env mark
    | ent :: ents =>
      match ent with
      | Entry.rename name' mark' _ => if name = name' ∧ mark = mark' then ent else lookup_entry ents
      | Entry.syn name' mark' _ =>  if name = name' ∧ mark = mark' then ent else lookup_entry ents
      | Entry.keyword name' => if name = name' then ent else lookup_entry ents
    let result := lookup_entry ents;
    if let none := result then lookup_aux env mark else result;
  lookup_aux env mark

#eval Name.lookup test3

abbrev Env {S T: Type} := List (S × T)
def Env.lookup {S T: Type} [DecidableEq S] (key: S) (env: @Env S T) :=
  env.find? (λk' => k'.1 = key)

def eval_syntax {S T: Type} {setting: @Setting S} [DecidableEq S] [DecidableEq T] (p: @Pair (@Name S T)) (env: List (T × @Pair (@Name S T))) : @Pair (@Name S T) :=
match p with
| Pair.nil => Pair.nil
| Pair.atom s =>
  if let some ent := Name.lookup s then
    match ent with
    | Entry.rename _ _ new_name =>
      if let some v := Env.lookup new_name env then v.2
      else sorry
    | Entry.syn _ _ defi => sorry
    | Entry.keyword name => sorry
  else sorry
| Pair.cons car cdr => sorry
/-
環境を考慮して一意になるようにrename
TODO: 書く
-/
def NameToIdent {n: Nat} (env: @SynEnv String Ident n): @Name String Ident → Ident
| Name.ident name env mark => (name, 0)
| Name.lit lit => (lit, 0)
