def Bijection_on_Nat := {f: Nat → Nat // (∀y: Nat, ∃x: Nat, f x = y) ∧ (∀x x', f x = f x' → x = x')}

def lbp {p : Nat → Prop} (m n : Nat) : Prop := m = n + 1 ∧ ∀ k, k ≤ n → ¬p k

def wf_lbp {p : Nat → Prop} [DecidablePred p] (H : ∃n, p n) : WellFounded (@lbp p) := by {
  have ⟨n, pn⟩ := H;
  constructor;
  have : ∀m k, n ≤ k + m → Acc (@lbp p) k := by {
    intro m;
    induction m;
    case zero => {
      simp;
      intro k h;
      constructor;
      intro y ⟨l, r⟩;
      specialize r n h;
      contradiction;
    };
    case succ m m_ih => {
      intro k;
      induction k;
      case zero => {
        simp;
        intro h1;
        constructor;
        intro y ⟨h2l, h2r⟩;
        simp [h2l];
        apply m_ih;
        simp [Nat.add_comm, Nat.add_succ];
        assumption;
      };
      case succ k k_ih => {
        intro h1;
        constructor;
        intro y ⟨h2l, h2r⟩;
        apply m_ih;
        simp [h2l, Nat.add_assoc, Nat.add_comm 1, Nat.add_succ m];
        assumption;
      };
    };
  };
  intro a;
  exact this n a $ Nat.le_add_left n a;
}


#check @Nat.recOn
#check @Nat.rec
#check @WellFounded.fix
#eval Lean.versionString

variable {α : Sort u} {C : α → Sort v} {r : α → α → Prop}

unsafe def fix'.impl (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x :=
  F x fun y _ => impl hwf F y

set_option codegen false in
@[implementedBy fix'.impl]
def fix' (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x := hwf.fix F x