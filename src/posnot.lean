import Lean

abbrev ℕ := Nat
abbrev PositionalNotation {b: {n: ℕ // n > 1}} := List (Fin b)
def PositionalNotation.toNat {b: {n: ℕ // n > 1}} (pn: PositionalNotation) :=
  List.foldr (λ (a:Fin b) (n:Nat) => a + n * b) 0 pn

theorem hodai1: ∀x y:Nat, x ≥ 2 → y ≥ 2 → y ≤ x → x - y + 1 < x := by {
  intro x;
  induction x;
  simp;
  case succ x x_ih => {
    intro y;
    induction y;
    simp;
    case succ y y_ih => {
      intro h1 h2 h3;
      specialize y_ih h1;
      simp [Nat.succ_sub_succ];
      byCases h4: x = 1;
      all_goals byCases h5: y = 1;
      simp_all;
      simp [h4] at h3;
      have h6 := Nat.le_antisymm h2 h3;
      have h7 := Eq.symm (Nat.succ.inj h6);
      contradiction;
      simp [h5];
      have h6 := Nat.lt_of_le_of_ne (Nat.le_of_succ_le_succ h1) (Ne.symm h4);
      apply Nat.add_lt_add_right;
      apply Nat.sub_lt;
      apply @Nat.lt_trans 0 1;
      simp;
      assumption;
      simp;
      have h6 := Nat.lt_of_le_of_ne (Nat.le_of_succ_le_succ h1) (Ne.symm h4);
      have h7 := Nat.succ_le_of_lt h6;
      have h8 := Nat.lt_of_le_of_ne (Nat.le_of_succ_le_succ h2) (Ne.symm h5);
      have h9 := Nat.succ_le_of_lt h8;
      specialize x_ih y h7 h9 (Nat.le_of_succ_le_succ h3);
      apply @Nat.lt_trans (x - y + 1) x;
      assumption;
      exact Nat.lt.base x;
    }
  }
}

theorem hodai2: ∀n m: Nat,  n > 0 → m ≥ 2 → n / m < n := by {
  intros n m h0 h1;
  induction n, m using Nat.div.inductionOn;
  case ind x y h2 h3 => {
    have po := Nat.eq_or_lt_of_le h2.right;
    have h4 := Nat.div_eq x y;
    apply Or.elim po;
    intro pu;
    rw [←pu];
    have pi := Nat.div_eq y y;
    have pe: 0 < y := by {
      apply @Nat.lt_of_lt_of_le 0 2;
      simp;
      assumption;
    }
    have q := Nat.le_refl y;
    simp [pe, q, pi, Nat.sub_self];
    have w := Nat.div_eq 0 y;
    simp [pe, (Nat.not_le_of_gt pe), w];
    exact Nat.lt_of_succ_le h1;
    intro hh;
    have hod := Nat.zero_lt_sub_of_lt hh;
    specialize h3 hod h1;
    simp [h4, h2];
    have h5 := Nat.add_lt_add_right h3 1;
    apply @Nat.lt_trans ((x - y) / y + 1) (x - y + 1);
    assumption;
    apply hodai1;
    exact Nat.le_trans h1 h2.right;
    assumption;
    exact h2.right;
  }
  case base x y h => {
    have h4 := Nat.div_eq x y;
    simp [h] at h4;
    rw [h4];
    assumption;
  }
}

theorem hodai3: ∀n: Nat, 0 / n = 0 := by {
  intro n;
  have h2 := Nat.div_eq 0 n;
  cases n;
  rw [h2];
  simp;
  case succ n => {
    rw [h2];
    have h3 := Nat.succ_pos n |> Nat.not_le_of_gt;
    simp [h3];
  }
}

theorem hodai4: ∀n: Nat, n > 0 → n / n = 1 := by {
  intro n h1;
  have h2 := Nat.div_eq n n;
  simp [h1, Nat.le_refl] at h2;
  simp [h2, Nat.sub_self, hodai3];
}

theorem hodai5: ∀n m k: Nat, m ≤ n → n + k - m = n - m + k := by {
  intro n m k;
  revert n m;
  induction k;
  simp;
  case succ k ih1 => {
    simp [Nat.add_succ];
    intro n m;
    revert n;
    induction m;
    simp;
    case succ m ih2 => {
      intro n;
      induction n;
      simp;
      intro h1;
      have h5 := Nat.eq_zero_of_le_zero h1;
      contradiction;
      case succ n ih3 => {
        intro h1;
        simp [Nat.succ_sub_succ];
        have h2 := Nat.le_of_succ_le_succ h1;
        have h3 := ih1 (Nat.succ n) m (Nat.le_step h2);
        have h4 := ih2 n h2;
        simp [←h4, Nat.succ_add];
        
      };
    };
  };
}

theorem hodai6: ∀n b, b > 1 → n % b < b := by {
  intro n b h1;
  apply Nat.mod_lt;
  apply Nat.lt_of_le_and_ne;
  exact Nat.zero_le b;
  apply Ne.symm;
  intro h3;
  rw [h3] at h1;
  contradiction;
}

theorem hodai7: ∀n m: Nat, n ≥ m → ¬m > n := by {
  intro n m h1;
  apply Or.elim $ Nat.eq_or_lt_of_le h1;
  all_goals intro h2;
  rw [h2];
  exact Nat.lt_irrefl n;
  intro h3;
  exact absurd (Nat.lt_trans h2 h3) (Nat.lt_irrefl m);
}

theorem hodai8: ∀n m: Nat, n % m + n / m * m = n := by {
  intro n m;
  induction n, m using Nat.div.inductionOn;
  case ind x y ih1 ih2 => {
    have h1 := Nat.div_eq x y;
    simp [h1, ih1, Nat.mod_eq_sub_mod, Nat.add_mul, ←Nat.add_assoc, ih2, ←hodai5, Nat.add_sub_self_right];
  };
  case base x y ih1 => {
    have h1 := Nat.div_eq x y;
    simp [h1, ih1];
    have h2 := Nat.mod_eq x y;
    simp [h2, ih1];
  };
}

def toPositionalNotation {base: {n: ℕ // n > 1}} (n: ℕ) : @PositionalNotation base :=
  if h': n < base then 
    [Fin.mk n h']
  else 
    have h1 := hodai6 n base base.property;
    have h3: n / base < n := by {
      apply hodai2;
      apply Or.elim $ Nat.lt_or_ge n base;
      intro;
      contradiction;
      intro h3;
      apply @Nat.lt_of_lt_of_le 0 base;
      apply @Nat.lt_trans 0 1;
      simp;
      exact base.property;
      assumption;
      apply Nat.succ_le_of_lt;
      exact base.property;
    };
    Fin.mk (n % base.val) h1 :: (toPositionalNotation (n / base))
  termination_by _ n => n

theorem PositionalNotation.induction.F.{u} {b: { n: Nat // n > 1}}
  (C : Nat → Sort u)
  (ind: ∀n, n ≥ b.val → C (n / b) → C n)
  (base: ∀n, ¬n ≥ b.val → C n)
  (n: Nat) (f: ∀x', x' < n → C x') : C n :=
  if h: n ≥ b then
    have h1: n / b < n := by {
      apply hodai2;
      apply Or.elim $ Nat.lt_or_ge n b;
      intro a;
      exact absurd h (Nat.not_le_of_gt a);
      intro;
      apply @Nat.lt_of_lt_of_le 0 b;
      apply @Nat.lt_trans 0 1;
      simp;
      exact b.property;
      assumption;
      apply Nat.succ_le_of_lt;
      exact b.property;
    };
    ind n h (f (n / b) h1)
  else base n h

theorem PositionalNotation.inductionOn.{u}
  (motive: Nat → Sort u)
  (x: Nat)
  (b: {n: Nat // n > 1}) -- koko hontou ha implicit ni sitai
  (ind: ∀x, x ≥ b.val → motive (x / b) → motive x)
  (base: ∀x, ¬x ≥ b.val → motive x)
  : motive x :=
  WellFounded.fix (measure id).wf (PositionalNotation.induction.F motive ind base) x

theorem toNat_toPosNot_eq_Nat {b: {n: Nat // n > 1}} :∀n, (@toPositionalNotation b n).toNat = n := by {
  intro n;
  induction n using PositionalNotation.inductionOn;
  assumption;
  case ind n ih1 ih2 => {
    unfold toPositionalNotation;
    apply Or.elim $ Nat.lt_or_ge n b;
    intro h2;
    simp [h2, PositionalNotation.toNat, List.foldr];
    intro h2;
    have h3 := hodai7 n b h2;
    simp [PositionalNotation.toNat] at ih2;
    simp [h3, PositionalNotation.toNat, List.foldr, ih2];
  };
}

variable (α : Sort u)
variable (r : α → α → Prop)

#check (Acc r : α → Prop)
#check @WellFounded.fix
#check 
