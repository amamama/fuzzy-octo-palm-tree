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

def Board (n: ℕ) := Fin n × Fin n → Fin n
structure sudoku (n: {m: ℕ // ∃r, r * r = m}) where
  board: Board n.val
  h_row: ∀num x: Fin n.val, ∃y: Fin n.val, board (x, y) = num
  h_col: ∀num y: Fin n.val, ∃x: Fin n.val, board (x, y) = num
  h_box: ∀num: Fin n.val, ∀i j: Fin n.property.1, ∃x y: Fin n.val, x / n.property.1 = i ∧ y / n.property.1 = j ∧ board (x, y) = num

def toBoard (b : {ll: List (List ℕ) //∃m r, ll.length = m ∧ r * r = m ∧ m > 0}) : Board b.property.1 :=
  λ(x, y) =>
    let l := List.get! ↑y b.val;
    let num := List.get! ↑x l;
    let h := b.property;
    have h1: b.property.1 > 0 := by {
      have h1' := h.1;
      have ⟨h221, h222, h223⟩ := h.2.2;
      assumption;
    };
    Fin.ofNat' num h1


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




def s: sudoku ⟨4, 2, rfl⟩ := {
  board := toBoard b,
  h_row := by {
    simp [b];
    simp [toBoard];
    intro num x;
    --unhygienic
    inductionFinTerm num with num lt {
      induction num;
      case zero => {
        inductionFinTerm x with n lt' {
          try rename_i n ih;
          try clear ih;
          induction n;
          {
            exists Fin.ofNat 0;
            simp [List.get!];
            apply congr;
            rfl;
            rfl;
          }
          {
            rename_i n ih;
            clear ih;
            induction n;
            case zero => {
              exists Fin.ofNat 2;
              simp [List.get!];
              apply congr;
              rfl;
              rfl;
            }
            {
              rename_i n ih;
              clear ih;
              induction n;
              case zero => {
                exists Fin.ofNat 1;
                simp [List.get!];
                apply congr;
                rfl;
                rfl;
              }
              case succ => {
                rename_i n ih;
                clear ih;
                induction n;
                case zero => {
                  exists Fin.ofNat 3;
                  simp [List.get!];
                  apply congr;
                  rfl;
                  rfl;
                }
                case succ => {
                  contradiction;
                }
              }
            }
          }
        }
      }
      case succ => {
        rename_i num n_ih;
        induction num;
        {
          inductionFinTerm x with n lt' {
            try rename_i n ih;
            try clear ih;
            induction n;
            {
              exists Fin.ofNat 3;
              simp [List.get!];
              rfl;
            }
            {
              try rename_i n ih;
              try clear ih;
              induction n;
              {
                exists Fin.ofNat 1;
                simp [List.get!];
                rfl;
              }
              {
                try rename_i n ih;
                try clear ih;
                induction n;
                {
                  exists Fin.ofNat 2;
                  simp [List.get!];
                  rfl;
                }
                {
                  try rename_i n ih;
                  try clear ih;
                  induction n;
                  {
                    exists Fin.ofNat 0;
                    simp [List.get!];
                    rfl;
                  }
                  {
                    contradiction;
                  }
                }
              }
            }
          }
        }
        {
          rename_i num n_ih;
          induction num;
          {
            inductionFinTerm x with n lt' {
              try rename_i n ih;
              try clear ih;
              induction n;
              {
                exists Fin.ofNat 1;
                simp [List.get!];
                rfl;
              }
              {
                try rename_i n ih;
                try clear ih;
                induction n;
                {
                  exists Fin.ofNat 3;
                  simp [List.get!];
                  rfl;
                }
                {
                  try rename_i n ih;
                  try clear ih;
                  induction n;
                  {
                    exists Fin.ofNat 0;
                    simp [List.get!];
                    rfl;
                  }
                  {
                    try rename_i n ih;
                    try clear ih;
                    induction n;
                    {
                      exists Fin.ofNat 2;
                      simp [List.get!];
                      rfl;
                    }
                    {
                      contradiction;
                    }
                  }
                }
              }
            }
          }
          {
            rename_i num n_ih hoge;
            induction num;
            {
              inductionFinTerm x with n lt' {
                try rename_i n ih;
                try clear ih;
                induction n;
                {
                  exists Fin.ofNat 2;
                  simp [List.get!];
                  rfl;
                }
                {
                  try rename_i n ih;
                  try clear ih;
                  induction n;
                  {
                    exists Fin.ofNat 0;
                    simp [List.get!];
                    rfl;
                  }
                  {
                    try rename_i n ih;
                    try clear ih;
                    induction n;
                    {
                      exists Fin.ofNat 3;
                      simp [List.get!];
                      rfl;
                    }
                    {
                      try rename_i n ih;
                      try clear ih;
                      induction n;
                      {
                        exists Fin.ofNat 1;
                        simp [List.get!];
                        rfl;
                      }
                      {
                        contradiction;
                      }
                    }
                  }
                }
              }
            }
            {
              contradiction;
            }                    
          }         
        }
      }
    }
  }
  h_col := sorry
  h_box := sorry
}


#check sudoku ⟨9, 3, rfl⟩


instance (n: {m: ℕ // ∃r, r * r = m}) : Repr (sudoku n) where
  reprPrec | _,  _ => "poyo"
