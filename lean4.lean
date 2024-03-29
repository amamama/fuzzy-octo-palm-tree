import Lean.Elab
open Lean.Elab.Tactic
open Lean.Elab

syntax (name := poyo) "foo" : tactic
@[tactic poyo]
def evalpoyo : Tactic := fun stx => do
  logInfo m!"<h1>{1}</h1>"

def Set (α : Type u) := α → Prop
def Set.in (s : Set α) (a : α) := s a

notation:50 a " ∈ " s:50 => Set.in s a

def Set.pred (p : α → Prop) : Set α := p

notation "{" a "|" p "}" => Set.pred (fun a => p)

def Set.union (s₁ s₂ : Set α) : Set α :=
  { a | a ∈ s₁ ∨ a ∈ s₂ }

infix:65 " ∪ " => Set.union

def Set.inter (s₁ s₂ : Set α) : Set α :=
  { a | a ∈ s₁ ∧ a ∈ s₂ }

infix:70 " ∩ " => Set.inter

instance (s : Set α) [h : Decidable (s a)] : Decidable (a ∈ Set.pred s) := h

instance (s₁ s₂ : Set α) [Decidable (a ∈ s₁)] [Decidable (a ∈ s₂)] : Decidable (a ∈ s₁ ∩ s₂) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (s₁ s₂ : Set α) [Decidable (a ∈ s₁)] [Decidable (a ∈ s₂)] : Decidable (a ∈ s₁ ∪ s₂) :=
  inferInstanceAs (Decidable (_ ∨ _))

def main : IO Unit :=
  IO.println "Hello, world!"

abbrev ℕ := Nat

def a := 1

#check ℕ
#check evalpoyo
#check (1,2,3)
#check 3 * 3 = 9
#check (⟨9, ⟨3, rfl⟩⟩:{m: ℕ // ∃r, r * r = m})


theorem test1 {α} (a b : α) (as bs : List α) (h : a::as = b::bs) : a = b :=
by {
  foo;
  skip;
  trace_state;
  injection h;
  assumption;
}



def b:{ll: List (List ℕ) //∃m r, ll.length = m ∧ r * r = m ∧ m > 0} :=
  ⟨[[0,3,2,1], [2,1,0,3], [3,0,1,2], [1,2,3,0]],
  by {
    let m := 4; let r := 2;
    exists m;
    exists r;
    simp;
  }⟩

macro "inductionFinTerm " term:term " with " v:ident lt:ident t:tacticSeq : tactic => `(induction $term with | mk $v $lt => $t)
syntax "repeatWithNat " term " => " tacticSeq : tactic
macro_rules
  | `(tactic| repeatWithNat $num => $seq) => `(tactic| first | let trialNum := $num; ($seq); repeatWithNat (Nat.succ $num) => $seq | skip)


def h: ∃x, x = 0 := Subtype.existsOfSubtype ⟨0, by rfl⟩
noncomputable def aaaa: Nat := sorry
#check Classical.choice
noncomputable def indefiniteDescription {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : {x // p x} :=
  Classical.choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩
noncomputable def hoge {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : Nonempty {x // p x} :=
let ⟨w, prop⟩ := h; ⟨w, prop⟩
--てすと,カタカナ，漢字．１２３ｂｃｓ

constant magic (h : ∃ n : ℕ, n > 0) : ℕ
axiom magic_extract (n h) : magic ⟨n, h⟩ = n

example : false :=
have h1 : magic ⟨1, sorry⟩ = 1 := magic_extract _ _;
have h2 : magic ⟨2, sorry⟩ = 2 := magic_extract _ _;
have proof_irrel : magic ⟨1, sorry⟩ = magic ⟨2, sorry⟩ := rfl;
absurd (h1.symm.trans $ proof_irrel.trans h2) sorry