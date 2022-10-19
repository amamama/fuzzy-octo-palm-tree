import Lean

abbrev ℕ := Nat
abbrev BaseType := {n: Nat // n > 1}
abbrev PositionalNotation {b: BaseType} := {d: List (Fin b) // d ≠ []}
def PositionalNotation.toNat {b: BaseType} (pn: PositionalNotation) :=
  List.foldr (λ (a:Fin b) (n:Nat) => a + n * b) 0 pn.val

theorem nand_iff: ∀ p q, ¬(p ∧ q) ↔ (p → ¬q) := by {
  intro p q;
  apply Iff.intro;
  intro h1 wp wq;
  exact absurd ⟨wp, wq⟩ h1;
  intro h1 wpq;
  exact h1 wpq.left wpq.right;
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
      by_cases h4: x = 1;
      all_goals by_cases h5: y = 1;
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
    };
    have q := Nat.le_refl y;
    simp [pe, q, pi, Nat.sub_self];
    have w := Nat.div_eq 0 y;
    simp [pe];
    simp [(Nat.not_le_of_gt pe)];
    rw [w];
    simp [h2];
    have := Nat.not_eq_zero_of_lt pe;
    simp [this];
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
      --intro h1;
      --have h5 := Nat.eq_zero_of_le_zero h1;
      --contradiction;
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

theorem hodai9: ∀n m k: Nat, (n + m) % k = ((n % k) + (m % k)) % k := by {
  intro n m k;
  revert m;
  induction n,k using Nat.mod.inductionOn;
  case ind x y prems ih => {
    intro m;
    have h1 := Nat.mod_eq x y;
    simp [prems] at h1;
    simp [h1, ←ih];
    have h2: y ≤ x + m := Nat.add_le_add prems.right (Nat.zero_le m);
    have h3 := Nat.mod_eq_sub_mod h2;
    simp [h3];
    have h4 := hodai5 x y m prems.right;
    simp [h4];
  };
  case base x y prems => {
    intro m;
    have h1 := Nat.mod_eq x y;
    simp [prems] at h1;
    simp [h1];
    induction m,y using Nat.mod.inductionOn;
    case ind x' y prems' ih => {
      have h2 := Nat.mod_eq x' y;
      simp [prems'] at h2;
      simp [h2];
      specialize ih prems h1;
      simp [←ih, Nat.add_comm x (x' - y)];
      have h3 := hodai5 x' y x prems'.right;
      simp [←h3];
      have h4 := Nat.add_le_add prems'.right (Nat.zero_le x);
      simp [Nat.add_comm] at h4;
      have h5 := Nat.mod_eq_sub_mod h4;
      simp [h5, Nat.add_comm];
    };
    case base x' y prems' => {
      have h1 := Nat.mod_eq x' y;
      simp [prems'] at h1;
      simp [h1];
    };
  };
}

theorem hodai10: ∀n, n / 1 = n := by {
  intro n;
  induction n;
  simp;
  case succ n ih => {
    have h1 := Nat.div_eq (Nat.succ n) 1;
    have h2: 1 ≤ Nat.succ n := Nat.succ_le_succ $ Nat.zero_le n;
    simp [h2, Nat.sub_succ, Nat.pred, ih] at h1;
    assumption;
  };
}

theorem hodai10_1: ∀n m k: Nat, m ≤ k → n - (k - m) = n + m - k := by {
  intro n m;
  revert n;
  induction m;
  simp;
  case succ m ih => {
    intro n k;
    revert n;
    induction k;
    intros n h;
    have h1 := Nat.not_succ_le_zero m h;
    contradiction;
    case succ k ih2 => {
      intro n h;
      simp [Nat.succ_sub_succ, Nat.add_succ];
      have h2 := Nat.le_of_succ_le_succ h;
      exact ih n k h2;
    };
  };
}

theorem hodai10_2: ∀ n m, n = n - m → n = 0 ∨ m = 0 := by {
  intro n m;
  revert n;
  induction m;
  simp;
  case succ m ih => {
    intro n h;
    induction n;
    simp;
    case succ n ih2 => {
      rw [Nat.succ_sub_succ] at h;
      have h1 := congrArg Nat.pred h;
      simp at h1;
      simp [Nat.sub_succ] at ih2;
      specialize ih2 h1;
      simp [ih2] at h;
    };
  };
}

theorem hodai10_3: ∀n m: Nat, n < n - m → False := by {
  intros n m;
  apply hodai7 n (n - m);
  exact Nat.sub_le n m;
}

theorem hodai10_5: ∀n m: Nat, n % m ≠ 0 → m - n % m = ((n / m * m + m) - n) % m := by {
  intro n m;
  induction n, m using Nat.mod.inductionOn;
  case ind x y prems ih => {
    have h1 := Nat.mod_eq x y;
    simp [prems] at h1;
    have h2 := Nat.div_eq x y;
    simp [prems] at h2;
    intro h;
    simp [h1, h2];
    simp [h1] at h;
    simp [ih h];
    rw [
      Nat.add_mul,
      Nat.one_mul,
      Nat.add_assoc _ y _,
      ←Nat.add_assoc];
      generalize h3: (x - y) / y * y + y = z;
      rw [hodai10_1];
      exact prems.right;
  };
  case base x y prems => {
    have h1 := Nat.mod_eq x y;
    simp [prems] at h1;
    have h2 := Nat.div_eq x y;
    simp [prems] at h2;
    simp [h1, h2];
    rw [nand_iff] at prems;
    apply Or.elim $ Nat.eq_or_lt_of_le $ Nat.zero_le y;
    intro a;
    simp [←a];
    intro a;
    specialize prems a;
    have h3 := Nat.mod_eq (y - x) y;
    have h4 := Nat.gt_of_not_le prems;
    by_cases h5: y ≤ y - x;
    apply Or.elim $ Nat.eq_or_lt_of_le h5;
    intro b;
    simp [←b];
    intro h;
    have h6: x = 0 := by {
      apply Or.elim $ hodai10_2 y x b;
      intro b;
      rw [b] at a;
      exact absurd a (Nat.lt_irrefl 0);
      intro;
      contradiction;
    };
    contradiction;
    intro b c;
    have := hodai10_3 y x b;
    contradiction;
    intro h6;
    simp [a, h5] at h3;
    rw [h3];
  };
}

theorem hodai10_6: ∀n m: Nat, n % m = 0 → m - n % m = m := by {
  intro n m h1;
  simp [*];
}

/-
theorem hodai11: ∀n m k: Nat, n > m → (n - m) % k = ((n % k) + (k - (m % k))) % k := by {
  intro n m k h1;
}

theorem hodai12: ∀n m k: Nat, (n * m) % k = ((n % k) * (m % k)) % k := by {
  intro n m k;
}
-/

theorem hodai12_1: ∀n m, m > 0 → n ≥ m → (n - m) % (m - 1) = (n - 1) % (m - 1) := by {
  intro n m h' h;
  have h1 := Nat.mod_eq (n - 1) (m - 1);
  by_cases h2: 0 < m - 1 ∧ m - 1 ≤ n - 1;
  simp [h2] at h1;
  simp [Nat.sub_sub] at h1;
  have h3: 1 + (m - 1) = m := by {
    simp [Nat.sub_succ];
    induction m;
    simp at h2;
    case succ m ih => {
      simp [Nat.add_comm];
    };
  };
  simp [h3] at h1;
  rw [h1];
  --
  simp [h2] at h1;
  rw [nand_iff] at h2;
  by_cases h3: 0 < m - 1;
  specialize h2 h3;
  have h6 := Nat.gt_of_not_le h2;
  have h7 := Nat.add_lt_add_right h6 1;
  have h10 := Nat.sub_add_cancel h';
  rw [h10] at h7;
  have h11: n > 0 := Nat.lt_of_lt_of_le h' h;
  have h12 := Nat.sub_add_cancel h11;
  rw [h12] at h7;
  apply Or.elim $ Nat.eq_or_lt_of_le h;
  intro a;
  simp [a];
  --
  intro a;
  have h13 := Nat.lt_trans a h7;
  exact absurd h13 $ Nat.lt_irrefl m;
  --
  have h4 := Nat.ge_of_not_lt h3 |> Nat.eq_zero_of_le_zero;
  simp [h4, Nat.mod_zero];
  have h5: m = 1 := by {
    have h6 := Nat.succ_le_of_lt h';
    have h7 := Nat.eq_add_of_sub_eq h6 h4;
    simp at h7;
    assumption;
  };
  simp [h5];
}

theorem hodai13: ∀n m k, m > 1 → (n + k) % (m - 1) = (n / m + n % m + k) % (m - 1) := by {
  intro n m;
  induction n,m using Nat.mod.inductionOn;
  case ind x y prems ih => {
    intro k h;
    specialize ih k h;
    have h1 := Nat.div_eq x y;
    have h2 := Nat.mod_eq x y;
    simp [prems] at h1;
    simp [prems] at h2;
    simp [h1, h2];
    simp [Nat.add_assoc, Nat.add_comm 1];
    simp [←Nat.add_assoc];
    rw [hodai9 _ 1, ←ih];
    by_cases h3: y > 2;
    have h4: y - 1 > 1 := by {
      have h5 := Nat.zero_lt_sub_of_lt h3;
      have h6 := Nat.succ_lt_succ h5;
      have h7 := hodai5 y 2 1 (Nat.le_of_lt h3);
      simp [Nat.add_succ] at h7;
      rw [←h7] at h6;
      simp [Nat.sub_succ];
      assumption;
    };
    have h5 := Nat.mod_eq_of_lt h4;
    rw [←hodai5 x y k prems.right];
    have h6 := hodai12_1 (x + k) y prems.left (Nat.add_le_add prems.right (Nat.zero_le k));
    simp [h6];
    rw [←hodai9];
    have h7 := Nat.lt_of_lt_of_le prems.left prems.right |> Nat.succ_le_of_lt;
    have h8 := Nat.add_le_add h7 (Nat.zero_le k);
    simp at h8;
    have h9 := hodai5 (x + k) 1 1 h8;
    rw [←h9, Nat.add_sub_self_right];
    --
    have h4 := Nat.ge_of_not_lt h3;
    have h5 := Nat.succ_le_of_lt h;
    have h6 := Nat.le_antisymm h4 h5;
    simp [h6, Nat.sub_succ, Nat.mod_one];
  };
  case base x y prems => {
    intro k h;
    have h1 := Nat.div_eq x y;
    simp [prems] at h1;
    simp [h1];
    have h2 := Nat.mod_eq x y;
    simp [prems] at h2;
    simp [h2];
  };
}

theorem ornot_then_nand: ∀p q, ¬p ∨ ¬q → ¬(p ∧ q) := by {
  intro p q wor wpq;
  apply Or.elim wor;
  all_goals {
    intros;
    have ⟨wp, wq⟩ := wpq;
    contradiction;
  }
}

def toPositionalNotation {base: BaseType} (n: ℕ) : @PositionalNotation base :=
  if h': n < base then 
    by {
      let ret := [Fin.mk n h'];
      have h: ret ≠ [] := by simp;
      exact ⟨ret, h⟩;
    }
  else 
    by {
      have h1 := hodai6 n base base.property;
      have h2: n / base < n := by {
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
      let ret := Fin.mk (n % base.val) h1 :: (toPositionalNotation (n / base)).val;
      have h: ret ≠ [] := by {simp;};
      exact ⟨ret, h⟩;
    }
  termination_by _ n => n

theorem PositionalNotation.induction.F.{u} {b: BaseType}
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
  (b: BaseType) -- koko hontou ha implicit ni sitai
  (ind: ∀x, x ≥ b.val → motive (x / b) → motive x)
  (base: ∀x, ¬x ≥ b.val → motive x)
  : motive x :=
  WellFounded.fix (measure id).wf (PositionalNotation.induction.F motive ind base) x

theorem toNat_toPosNot_eq_Nat {b: BaseType} : ∀n, (@toPositionalNotation b n).toNat = n := by {
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
    simp [hodai8];
  };
  case base x prems => {
    unfold toPositionalNotation;
    have h1 := Nat.gt_of_not_le prems;
    simp [h1, PositionalNotation.toNat, List.foldr];
  };
}

theorem keta_no_wa_no_amari_eq_moto_no_kazu_no_amari {b: {n: Nat // n > 1}} : ∀n m, (n + m) % (b.val - 1) = (List.foldl (λ(a: Nat) (b: Fin b) => a + b) m (toPositionalNotation n).val) % (b.val - 1) := by {
  intro n;
  induction n using PositionalNotation.inductionOn;
  assumption;
  case ind x prems ih => {
    unfold toPositionalNotation;
    have h1 := hodai7 x b prems;
    all_goals simp [List.foldl, h1, Nat.add_comm];
    intro m;
    specialize ih (m + x % b.val);
    simp [←ih];
    rw [(Nat.add_comm m), ←Nat.add_assoc];
    have h2 := hodai13 x b m b.property;
    assumption;
  };
  case base x prems => {
    unfold toPositionalNotation;
    have h1 := Nat.gt_of_not_le prems;
    simp [h1, List.foldl];
    intro;
    simp [Nat.add_comm];
  };
}

#eval Lean.versionString