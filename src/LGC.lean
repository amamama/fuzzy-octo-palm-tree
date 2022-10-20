@[simp]
def Periodic_with_period (f: Nat → Nat) (p: Nat): Prop := p > 0 ∧ ∀n, f (n + p) = f n
@[simp]
def Periodic (f: Nat → Nat) : Prop := ∃p, Periodic_with_period f p
@[simp]
def QuasiPeriodic_with_period (f: Nat → Nat) (p: Nat): Prop := ∃n0, ∀n, n ≥ n0 → f (n + p) = f n
@[simp]
def QuasiPeriodic (f: Nat → Nat) : Prop := ∃p, QuasiPeriodic_with_period f p


theorem mod_mod_eq_mod : ∀n m: Nat, n % m % m = n % m := by {
  intro n m;
  cases m;
  simp [Nat.mod_zero];
  case succ m => {
    have := Nat.mod_lt n (Nat.succ_pos m);
    simp [Nat.mod_eq_of_lt this];
  };
}

theorem add_mod_eq_mod : ∀n m: Nat, (n + m) % m = n % m := by {
  intro n m;
  have h1 := Nat.mod_eq (n + m) m;
  induction m;
  simp;
  simp [Nat.zero_lt_succ, Nat.le_add_left, Nat.add_sub_cancel] at h1;
  assumption;
}

theorem mul_mod_eq_zero : ∀n m: Nat, (n * m) % m = 0 := by {
  intro n m;
  induction n;
  simp;
  simp [Nat.succ_mul, add_mod_eq_mod];
  assumption;
}

theorem add_left_mod : ∀m n k: Nat, (k + m) % n = (k + m % n) % n := by {
  intro m n;
  induction m, n using Nat.mod.inductionOn with
  | ind x y ih1 ih2 => {
    intro k;
    rw [Nat.mod_eq x y];
    simp [ih1, ←ih2];
    rw [Nat.mod_eq];
    simp [ih1];
    have h1 := Nat.add_le_add  (Nat.zero_le k) (ih1.right);
    simp at h1;
    simp [h1, Nat.add_sub_assoc ih1.right];
  }
  | base x y h1 => {
    simp [Nat.mod_eq x y, h1];
  }
}

theorem add_right_mod : ∀m n k: Nat, (m + k) % n = (m % n + k) % n := by {
  intro m n;
  induction m, n using Nat.mod.inductionOn with
  | ind x y ih1 ih2 => {
    intro k;
    rw [Nat.mod_eq x y];
    simp [ih1, ←(ih2 k)];
    generalize h2 : x - y = z;
    have := Nat.eq_add_of_sub_eq ih1.right h2;
    rw [this, Nat.add_assoc, Nat.add_comm y, ←Nat.add_assoc, add_mod_eq_mod];
  }
  | base x y h1 => {
    simp [Nat.mod_eq x y, h1];
  }
}

theorem add_mod : ∀l m n: Nat, (l + m) % n = (l % n + m % n) % n := by {
  intro l m n;
  have h1 := add_left_mod m n (l % n);
  rw [←h1];
  exact add_right_mod l n m;
}

theorem mul_left_mod : ∀m n k: Nat, (k * m) % n = (k * (m % n)) % n := by {
  intro m n;
  induction m, n using Nat.mod.inductionOn with
  | ind x y ih1 ih2 => {
    rw [Nat.mod_eq];
    simp [*];
    intro k;
    rw [←ih2, Nat.mul_sub_left_distrib];
    induction k;
    simp;
    case succ k ih => {
      rw [Nat.succ_mul k x, Nat.succ_mul k y];
      rw [←Nat.sub_sub, Nat.add_comm, Nat.add_sub_assoc (Nat.mul_le_mul_left k ih1.right)];
      rw [Nat.add_comm x (k * x - _), Nat.add_sub_assoc ih1.right];
      rw [@add_mod _ (x - y), ←ih, ←add_mod, Nat.add_comm];
      rw [Nat.mod_eq];
      have := Nat.add_le_add (Nat.zero_le (k * x)) ih1.right;
      simp_all
      simp [Nat.add_sub_assoc ih1.right];
    };
  }
  | base x y h1 => {
    intro k;
    rw [Nat.mod_eq x y];
    simp [h1];
  }
}

theorem mul_right_mod : ∀m n k: Nat, (m * k) % n = ((m % n) * k) % n := by {
  intro m n;
  induction m, n using Nat.mod.inductionOn with
  | ind x y ih1 ih2 => {
    rw [Nat.mod_eq];
    simp [*];
    intro k;
    rw [←ih2, Nat.mul_sub_right_distrib];
    induction k;
    simp;
    case succ k ih => {
      rw [Nat.mul_comm, Nat.succ_mul k x, Nat.mul_comm y, Nat.succ_mul k y];
      rw [←Nat.sub_sub, Nat.add_comm, Nat.add_sub_assoc (Nat.mul_le_mul_left k ih1.right)];
      rw [Nat.add_comm x (k * x - _), Nat.add_sub_assoc ih1.right];
      rw [Nat.mul_comm k x, Nat.mul_comm k y];
      rw [add_mod _ (x - y), ←ih, ←add_mod, Nat.add_comm];
      rw [Nat.mod_eq];
      have := Nat.add_le_add (Nat.zero_le (x * k)) ih1.right;
      simp_all
      simp [Nat.add_sub_assoc ih1.right];
    };
  }
  | base x y h1 => {
    intro k;
    rw [Nat.mod_eq x y];
    simp [h1];
  }
}

theorem mul_mod : ∀l m n: Nat, (l * m) % n = ((l % n) * (m % n)) % n := by {
  intro l m n;
  have h1 := mul_left_mod m n (l % n);
  rw [←h1];
  exact mul_right_mod l n m;
}

theorem lt_of_add_const {m n} : ∀k: Nat, m < n → m < n + k := by {
  intro k h1;
  induction k;
  simp;
  assumption;
  case succ k ih => {
    have := Nat.add_lt_add ih Nat.zero_lt_one;
    assumption;
  };
}

theorem hoge {p q: Prop} : p → ¬(p ∧ q) → ¬q := by {
  intro ph nphqh qh;
  have : p ∧ q := ⟨ph, qh⟩;
  contradiction;
}

theorem odd_mod_even_is_odd : ∀m n, ((2 * m + 1) % (2 * n)) % 2 = 1 := by {
  intro m n;
  
  induction m, n using Nat.mod.inductionOn with
  | ind x y ih1 ih2 => {
    rw [Nat.mod_eq _ (2 * y)];
    have : 0 < 2 := by simp;
    have h1 := Nat.mul_lt_mul_of_pos_left ih1.left this;
    simp at h1;
    simp [h1];
    have h2 := Nat.mul_le_mul_left 2 ih1.right;
    have h3 := Nat.add_le_add h2 (Nat.zero_le 1);
    simp at h3;
    simp [h3];
    simp [Nat.mul_sub_left_distrib] at ih2;
    rw [Nat.add_comm, Nat.add_sub_assoc h2, Nat.add_comm];
    assumption; 
  }
  | base x y h1 => {
    rw [Nat.mod_eq _ (2 * y)];
    cases y;
    simp;
    rw [add_right_mod, Nat.mul_comm, mul_mod_eq_zero];
    simp;
    case succ y => {
      have h2 := hoge (Nat.zero_lt_succ y) h1;
      have h3: ¬2 * Nat.succ y ≤ 2 * x + 1 := by {
        have h4 := Nat.gt_of_not_le h2;
        have h5 := Nat.le_of_lt_succ h4 |> Nat.succ_le_succ;
        have h6 := Nat.mul_le_mul_left 2 h5;
        rw [Nat.mul_comm, Nat.succ_mul, Nat.add_comm, Nat.succ_add] at h6;
        have h7 := Nat.lt_of_succ_le h6;
        rw [Nat.add_comm, Nat.mul_comm x] at h7;
        exact Nat.not_le_of_gt h7;
      };
      simp [h3];
      rw [add_right_mod, Nat.mul_comm, mul_mod_eq_zero];
      simp;
    };
  }
}

theorem mod_eq_zero_of_add_mod : ∀{m n k}, (k + m) % n = m % n → k % n = 0 := by {
  intro m n k h1;
  rw [add_mod] at h1;
  induction k, n using Nat.mod.inductionOn with
  | ind x y ih1 ih2 => {
    rw [Nat.mod_eq];
    simp [ih1];
    rw [Nat.mod_eq x y] at h1;
    simp [ih1] at h1;
    specialize ih2 h1;
    assumption;
  }
  | base x y h2 => {
    rw [Nat.mod_eq];
    simp [h2];
    rw [Nat.mod_eq x y] at h1;
    simp [h2] at h1;
    rw [←add_left_mod m y x] at h1;
    induction m, y using Nat.mod.inductionOn with
    | ind x1 y1 ih1 ih2 => {
      rw [Nat.mod_eq] at h1;
      have := Nat.add_le_add (Nat.zero_le x) ih1.right;
      simp at this;
      simp [ih1, this, Nat.add_sub_assoc, Nat.mod_eq x1 y1] at h1;
      specialize ih2 h2 h1;
      assumption;
    }
    | base x1 y1 h3 => {
      simp [Nat.mod_eq x1 y1, h3] at h1;
      cases y1;
      simp [Nat.mod_zero] at h1;
      apply Nat.add_right_cancel;
      case m => {exact x1};
      simp;
      assumption;
      case succ n => {
        have h4 := Nat.zero_lt_succ n;
        have h5 := hoge h4 h2 |> Nat.gt_of_not_le;
        have h6 := hoge h4 h3 |> Nat.gt_of_not_le;
        cases x;
        simp;
        case succ x => {
          simp_all;
          rw [Nat.mod_eq] at h1;
          simp [h4] at h1;
          by_cases h8: Nat.succ n ≤ Nat.succ x + x1;
          simp [h8] at h1;
          rw [Nat.mod_eq] at h1;
          simp [h4] at h1;
          have : ¬Nat.succ n ≤ Nat.succ x + x1 - Nat.succ n := by {
            intro nh;
            have h9 := Nat.le_of_lt_succ h6;
            have h10 := Nat.le_of_lt_succ h5;
            have h11 := Nat.add_le_add h9 h10;
            have h12 := Nat.add_le_of_le_sub h8 nh;
            rw [Nat.add_comm] at h11;
            have h13 := Nat.le_trans (Nat.le_trans h12 h11) (Nat.le_succ (n + n));
            simp [Nat.succ_add, Nat.add_comm n] at h13;
            have h14 := Nat.not_succ_le_self (Nat.succ (n + n));
            contradiction;
          };
          simp [this] at h1;
          have := congrArg (λx => Nat.succ n + x) h1;
          simp [←Nat.add_sub_assoc h8, Nat.add_sub_cancel_left] at this;
          have h9 := Nat.add_right_cancel this;
          simp at h9;
          have h10 := Nat.lt_of_succ_lt_succ h5;
          rw [h9] at h10;
          have := Nat.lt_irrefl n;
          contradiction;
          simp [*] at h1;
          conv at h1 => {
            rhs
            rw [←Nat.zero_add x1]
          };
          have h11 := Nat.add_right_cancel h1;
          simp at h11;
        };
      };
    }
  }
}

def f1 n := n % 3
theorem t1 : Periodic f1 := by {
  rw [Periodic];
  exists 3;
  simp [f1, add_mod_eq_mod];
}

def f2
| 0 => 4
| n + 1 => (3 * f2 n) % 7

theorem t2 : Periodic f2 := by {
  simp;
  exists 6;
  simp;
  intro n;
  simp [f2];
  rw [←mul_left_mod (3 * f2 n) 7 3];
  rw [←mul_left_mod (3 * (3 * f2 n)) 7 3];
  rw [←mul_left_mod (3 * (3 * (3 * f2 n))) 7 3];
  rw [←mul_left_mod (3 * (3 * (3 * (3 * f2 n)))) 7 3];
  rw [←mul_left_mod (3 * (3 * (3 * (3 * (3 * f2 n))))) 7 3];
  rw [←Nat.mul_assoc];
  rw [←Nat.mul_assoc];
  rw [←Nat.mul_assoc];
  rw [←Nat.mul_assoc];
  rw [←Nat.mul_assoc];
  have : 3 * 3 * 3 * 3 * 3 * 3 = 729 := rfl;
  rw [this, mul_mod];
  have : 729 % 7 = 1 := rfl;
  simp [this, mod_mod_eq_mod];
  cases n;
  simp;
  simp [f2, mod_mod_eq_mod];
}

theorem t3 : ∀l m n, let f := (λx: Nat => (x * (4 * l + 1) + (2 * m + 1)) % (2^n)); Periodic_with_period f (2^n) ∧ ∀ M, M < (2^n) → ¬Periodic_with_period f M := by {
  intro l m n;
  simp;
  generalize hM : 2 ^ n = M;
  generalize ha : 4 * l = A;
  generalize hc : 2 * m + 1 = c;

  have hoge: ∀n: Nat, 2 ^ n > 0 := by {
    intro n;
    induction n;
    simp;
    case succ n ih => {
      have := Nat.mul_lt_mul_of_pos_right ih (Nat.zero_lt_succ 1);
      simp at this;
      simp[Nat.pow_succ, this];
    };
  };

  apply And.intro;
  case left => {
    cases M;
    simp;
    specialize hoge n;
    simp [hM] at hoge;
    simp [Nat.zero_lt_succ];
    intro x;
    rw [Nat.add_mul, Nat.add_assoc, Nat.add_comm _ c, ←Nat.add_assoc, Nat.mul_comm (Nat.succ _), add_mod, mul_mod_eq_zero];
    simp [mod_mod_eq_mod];
  };
  case right => {
    intro M0 h1 ⟨h2l, h2r⟩;
    have h3 := h2r 0;
    simp at h3;
    rw [←ha, ←hc, ←hM] at h3;
    cases n;
    simp [Nat.pow_zero, Nat.mod_one] at h3;
    simp [Nat.pow_zero] at hM;
    rw [←hM] at h1;
    have a := Nat.le_of_lt_succ h1;
    simp [Nat.le_zero_eq M0] at a;
    rw [a] at h2l;
    contradiction;
    case succ n => {
      simp [Nat.pow_succ] at h3;
      have h4 := odd_mod_even_is_odd m (2 ^ n);
      rw [add_mod] at h3;
      conv at h3 => {
        rhs;
        rw [←mod_mod_eq_mod];
      };
      have h5 := mod_eq_zero_of_add_mod h3;
      rw [mod_mod_eq_mod] at h5;
     };
  };
}
