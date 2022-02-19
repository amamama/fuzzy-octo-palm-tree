abbrev ℕ := Nat
def PositionalNotation {n: ℕ} {h: n > 1} := List (Fin n)
def PositionalNotation.toNat {n: ℕ} {h: n > 1}  :=
  List.foldr (λ (a:Fin n) (b:Nat) => a + b * 10) 0

theorem hodai0: ∀n m: Nat, n < m → 0 < m - n := by {
  intro n;
  induction n;
  simp;
  intros;
  assumption;
  case succ n ih => {
    intro m;
    induction m;
    intro h1;
    have h2 := Nat.not_lt_zero (Nat.succ n);
    contradiction;
    case succ m ih2 => {
      simp [Nat.succ_sub_succ];
      intro h2;
      have h3 := Nat.lt_of_succ_lt_succ h2;
      exact ih m h3;
    }
  }
}

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
    have hod := hodai0 y x hh;
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

def toPositionalNotaion {base: ℕ} {h: base > 1} (n: ℕ) : @PositionalNotation base h :=
  if h': n < base then 
    [Fin.mk n h']
  else by {
    have h1: base > 1 → n % base < base := by {
      intro h2;
      apply Nat.mod_lt;
      apply Nat.lt_of_le_and_ne;
      exact Nat.zero_le base;
      apply Ne.symm;
      intro h3;
      rw [h3] at h2;
      contradiction;
    };
    exact Fin.mk (n % base) (h1 h) :: @toPositionalNotaion base h (n / base);
  }
  termination_by _ n => n
  decreasing_by {
    simp [invImage, InvImage, Prod.lex, sizeOfWFRel, measure, Nat.lt_wfRel, WellFoundedRelation.rel];
    specialize h1 h;
    apply hodai2;
    have h2 := Nat.lt_or_ge n base;
    apply Or.elim h2;
    intro;
    contradiction;
    intro h3;
    apply @Nat.lt_of_lt_of_le 0 base;
    apply @Nat.lt_trans 0 1;
    simp;
    assumption;
    assumption;
    apply Nat.succ_le_of_lt;
    assumption;

  }