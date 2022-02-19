abbrev ℕ := Nat
def bije {α β} (f: α → β) := ∀y: β, ∃x: α, f x = y ∧ (∀x', f x = f x' → x = x')
def bije_contraposition {α β} {f: α → β} (h: bije f) : ∀y, ∃x, f x = y ∧ (∀x', x ≠ x' → f x ≠ f x') := by {
  intro y;
  simp [bije] at h;
  have ⟨w, ⟨hl, hr⟩⟩ := h y;
  exists w;
  apply And.intro;
  assumption;
  intro x' h1 h2;
  specialize hr x' h2;
  contradiction;
}
def Bijection (α β) := {f: α → β // bije f}

def Bijection.comp {α β γ} (g: Bijection β γ) (f: Bijection α β) : Bijection α γ := ⟨λx => g.val (f.val x), by {
  simp [bije] at *;
  intro y;
  have ⟨gw, ⟨hgl, hgr⟩⟩ := g.property y;
  have ⟨fw, ⟨hfl, hfr⟩⟩ := f.property gw;
  exists fw;
  apply And.intro;
  case left => {
    rw [hfl, hgl];
  };
  case right => {
    intro x';
    intro h;
    rw [hfl, hgl] at h;
    rw [hgl] at hgr;
    have h1 := hgr (f.val x') h;
    rw [h1] at hfl;
    exact hfr x' hfl;
  };
}⟩

instance {α: Type u} {β: Type v} {γ: Type w} : HMul (Bijection β γ) (Bijection α β) (Bijection α γ) where hMul := Bijection.comp
instance {α: Type u} : Mul (Bijection α α) where mul := Bijection.comp

theorem Bijection.assoc {α β γ δ} : ∀(a: Bijection γ δ) (b: Bijection β γ) (c: Bijection α β), (a * b) * c = a * (b * c) := by {
  intros;
  rfl;
}

def Bijection.id {α} : Bijection α α := ⟨λ x => x, by {
  simp [bije];
  intro y;
  exists y;
  simp;
  intros;
  assumption;
}⟩

theorem Bijection.leftIdentity {α β} : ∀f: Bijection α β, @Bijection.id β * f = f := by {
  intro f;
  induction f with
  | mk v p => {
    rfl;
  };
}
theorem Bijection.rightIdentity {α β} : ∀f: Bijection α β, f = f * @Bijection.id α := by {
  intro f;
  induction f with
  | mk v p => {
    rfl;
  };
}

def Bijection.inv {α β} (f: Bijection α β) : Bijection β α := ⟨λy => (f.property y).1, by {
  simp [bije];
  intro x;
  have ⟨hl, hr⟩ := (f.property (f.val x)).2;
  specialize hr x hl;
  exists f.val x;
  simp;
  rw [hr];
  apply And.intro;
  case left => {
    rfl;
  };
  case right => {
    intro x';
    intro h1;
    have ⟨hlx', hrx'⟩ := (f.property x').2;
    rw [←h1] at  hlx';
    assumption;
  };
}⟩

postfix:max "⁻¹" => Bijection.inv

theorem Bijection.leftInverse {α β} : ∀f: Bijection α β, f⁻¹ * f = id := by {
  intro f;
  have h: ∀x, (f⁻¹ * f).val x = id.val x := by {
    intro x;
    simp [inv, HMul.hMul, comp];
    induction f with
    | mk f p => {
      have ⟨h1l, h1r⟩ := (p (f x)).2;
      specialize h1r x h1l;
      rw [h1r];
      rfl;
    };
  };
  exact Subtype.eq (funext h);
}
theorem Bijection.rightInverse {α β} : ∀f: Bijection α β, id = f * f⁻¹ := by {
  intro f;
  have h: ∀x, id.val x = (f * f⁻¹).val x := by {
    intro x;
    --generalize h: f⁻¹ = f';
    simp [inv, HMul.hMul, comp] at *;
    induction f with
    | mk f p => {
      simp;
      have ⟨h1l, h1r⟩ := (p x).2;
      rw [h1l];
      rfl;
    }
  };
  exact Subtype.eq (funext h);
}

def Perm (n: ℕ) := Bijection (Fin n) (Fin n)
instance {n: ℕ} : Mul (Perm n) where mul := Bijection.comp
def Perm.id {n: ℕ} : Perm n := @Bijection.id (Fin n)
def Transposition {n: ℕ} (i j: Fin n) := {t: Perm n // i.val < j.val ∧ t.val i = j ∧ t.val j = i ∧ ∀k: Fin n, k ≠ i ∧ k ≠ j → t.val k = k}
instance {n: ℕ} : Coe (Fin n) (Fin (n + 1)) :=
  ⟨λx => ⟨x.val, Nat.lt.step x.isLt⟩⟩
instance {n: ℕ} : Coe (Perm n) (Perm (n + 1)) :=
  ⟨λp => ⟨λx => if h: x < n then ↑(p.val ⟨x, h⟩) else x, by {
    simp [bije];
    intro y;
    have h2 := Nat.lt_irrefl n;
    byCases h: y = n;
    case inl => {
      exists y;
      rw [h];
      simp [h2];
      intro x' h1;
      induction x' with
      | mk v lt => {
        byCases h3: v = n;
        simp [h3, h2] at h1;
        assumption;
        have h4 := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ lt) h3;
        simp [h4] at h1;
        generalize h5: p.val ⟨v, h4⟩ = v';
        rw [h5] at h1;
        have h6: y.val < n := by {
          rw [h1];
          exact v'.isLt;
        };
        rw [h] at h6;
        contradiction;
      };
    };
    case inr => {
      have h1: y.val < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ y.isLt) h;
      have ⟨w, ⟨h2l, h2r⟩⟩ := p.property ⟨y.val, h1⟩;
      let w': Fin (n + 1) := ↑w;
      exists w';
      have h3: w'.val < n := w.isLt;
      have h4: ⟨w'.val, h3⟩ = w := Fin.eq_of_val_eq rfl;
      simp [h3];
      apply And.intro;
      case left => {
        rw [h4, h2l];
      };
      case right => {
        intro x' h5;
        rw [h4] at h5;
        rw [h2l] at h5;
        induction x' with
        | mk v lt => {
          byCases h6: v = n;
          simp [h6, h2] at h5;
          have h7: y.val = v := Eq.trans h5 (Eq.symm h6);
          rw [h6] at h7;
          contradiction;
          have h8 := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ lt) h6;
          simp [h8] at h5;
          generalize h9: (⟨v, h8⟩:Fin n) = v';
          generalize h10: (⟨y, h1⟩:Fin n) = y';
          rw [h9] at h5;
          rw [h10] at h2l;
          have h11: y' = p.val v' := by {
            have h12 := @Fin.eq_of_val_eq (n+1) y (p.val v') h5;
            rw [←h10];
            apply Fin.eq_of_val_eq;
            assumption;
          };
          rw [h11] at h2l;
          specialize h2r v' h2l;
          apply Fin.eq_of_val_eq;
          have h12: v = v'.val := by {
            have h13 := Fin.val_eq_of_eq h9;
            simp at h13;
            assumption;
          };
          simp;
          rw [h12];
          have h13 := Fin.val_eq_of_eq h2r;
          assumption;
        };
      };
    };
  }⟩⟩

theorem perm_compose_trans {n: ℕ} : ∀p: Perm (n + 1), ∃q: Perm n, p = ↑q * Perm.id ∨ ∃i: Fin (n + 1), ∃t: Transposition i (Fin.ofNat n), p = t.val * ↑q := by {
  --Perm (n + 1) からPerm nを構成して p n = n かどうかで場合分け
  --intro perm;
  --let ⟨p, h⟩ := perm;
  intro ⟨p, h⟩;
  let nFin: Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩;
  generalize pn: p nFin = pnFin;
  let downcast: (x: Fin (n + 1)) → (x ≠ nFin) → Fin n := λx h => ⟨x.val, by {
    have h1 := x.isLt;
    byCases h2: x.val = nFin.val;
    have h3 := Fin.eq_of_val_eq h2;
    contradiction;
    simp at h2;
    have h4 := Nat.le_of_succ_le_succ (Nat.succ_le_of_lt h1);
    exact Nat.lt_of_le_of_ne h4 h2;
  }⟩;
  have downcast_aux: ∀x: Fin n, ↑x ≠ nFin := by {
    intro x h;
    have h1 := x.isLt;
    byCases h2: x = n;
    rw [h2] at h1;
    have h3 := Nat.lt_irrefl n;
    contradiction;
    have h3 := Fin.val_eq_of_eq h;
    simp at h3;
    contradiction;
  };
  have ltn: ∀x:Fin (n + 1), x ≠ nFin → x < n := by {
    intro x h2;
    have h1 := x.isLt;
    have h2 := Fin.val_ne_of_ne h2;
    apply Nat.lt_of_le_and_ne;
    apply Nat.le_of_lt_succ;
    assumption;
    exact h2;

  };
  have coe_downcast: ∀(x: Fin (n + 1)) h, ↑(downcast x h) = x := by {
    intro x h;
    apply Fin.eq_of_val_eq;
    rfl;
  };
  --whnFinは nFin = p whnFinとなるような数．
  have ⟨whnFin, ⟨prop_hnFinl, prop_hnFinr⟩⟩ := h nFin;
  have ⟨whpnFin, ⟨prop_hpnFinl, prop_hpnFinr⟩⟩ := h (p nFin);
  --写した先がnFinなら代わりにpnFinを返し，それ以外は p xを返す関数
  let f: Fin n → Fin n := λx => ⟨if cond: ↑x = whnFin then pnFin else p ↑x, by {
    have f_aux: ∀x, x ≠ whnFin → p x < n := by {
      intros x h3;
      byCases h4: (p x) < n;
      assumption;
      have h5 := (p x).isLt;
      have h6: (p x).val = n := by {
        apply Nat.le_antisymm;
        apply Nat.le_of_lt_succ;
        assumption;
        have h7: ∀m n: Nat, ¬(m < n) → n ≤ m := by {
          intro m n h;
          have or := Nat.lt_or_ge m n;
          cases or with
          | inl contra => contradiction
          | inr assum => assumption
        };
        exact h7 (p x).val n h4;
      };
      specialize prop_hnFinr x;
      have h7: n = nFin.val := rfl;
      have h9 := Fin.eq_of_val_eq (Eq.trans h6 h7);
      rw [h9] at prop_hnFinr;
      specialize prop_hnFinr prop_hnFinl;
      exact absurd (Eq.symm prop_hnFinr) h3;
    };
    byCases h1: nFin = p nFin;
    all_goals byCases h2: ↑x = whnFin;
    all_goals simp [h2];
    specialize prop_hnFinr nFin (Eq.trans prop_hnFinl h1);
    have _ := downcast_aux x;
    have _ := Eq.trans h2 prop_hnFinr;
    contradiction;
    rotate_left;
    have h3: nFin ≠ whnFin := by {
      intro h2;
      rw [←h2] at prop_hnFinl;
      rw [prop_hnFinl] at h1;
      simp at h1;
    };
    specialize f_aux nFin h3;
    rw [pn] at f_aux;
    assumption;
    all_goals exact f_aux x h2;
  }⟩;
  let q: Perm n := ⟨f, by {
    simp [bije];
    intro y;
    byCases h1: nFin = p nFin;
    case inl => {
      specialize prop_hnFinr nFin (Eq.trans prop_hnFinl h1);
      have h3: ∀x: Fin n, ↑x ≠ whnFin := by {
        intro x;
        rw [prop_hnFinr];
        exact downcast_aux x;
      };
      have ⟨w, ⟨h4l, h4r⟩⟩ := h ↑y;
      have h5 := h3 y;
      byCases h6: w = whnFin;
      rw [h6, prop_hnFinl, ←prop_hnFinr] at h4l;
      exact absurd (Eq.symm h4l) h5;
      rw [prop_hnFinr] at h6;
      let w' := downcast w h6;
      exists w';
      simp;
      apply And.intro;
      case left => {
        apply Fin.eq_of_val_eq;
        simp;
        have h7 := Fin.val_eq_of_eq h4l;
        have h8: (↑y:Fin (n + 1)).val = y.val := rfl;
        rw [←h8, ←h7];
        specialize h3 w';
        simp [h3];
      };
      case right => {
        intro x' h7;
        have w'_ne := h3 w';
        have x'_ne := h3 x';
        generalize h8: { val := w.val, isLt := (_ : w'.val < Nat.succ n): Fin (n + 1)} = w'';
        generalize h9: { val := x'.val, isLt := (_ : x'.val < Nat.succ n): Fin (n + 1)} = x'';
        --rw [h8, h9] at h7;
        simp [w'_ne, x'_ne] at h7;
        apply Fin.eq_of_val_eq;
        simp;
        have h10 := Fin.val_eq_of_eq h9;
        simp at h10;
        rw [h10];
        apply Fin.val_eq_of_eq;
        apply h4r;
        have h11 := Fin.eq_of_val_eq h7;
        simp [←h9];
        rw [←h11];
        /-
        have h12 := Fin.val_eq_of_eq h8;
        simp at h12;
        apply congrArg;
        apply Fin.eq_of_val_eq;
        assumption;
        -/
      };
    };
    case inr => {
      have h3: nFin ≠ whnFin := by {
        intro h4;
        rw [←h4] at prop_hnFinl;
        exact absurd (Eq.symm prop_hnFinl) h1;
      };
      byCases h4: ↑y = pnFin;
      case inl => {
        exists downcast whnFin (Ne.symm h3);
        have h5 := coe_downcast whnFin (Ne.symm h3);
        have h6: y.val = pnFin.val := Fin.val_eq_of_eq h4;
        apply And.intro;
        case left => {
          apply Fin.eq_of_val_eq;
          simp [h6, h5];
        };
        case right => {
          intro x' h7;
          simp [h5] at h7;
          byCases h8: ↑x' = whnFin;
          apply Fin.eq_of_val_eq;
          simp;
          have h9 := Eq.symm (Fin.val_eq_of_eq h8);
          assumption;
          simp [h8] at h7;
          have h10: ↑x' ≠ nFin := by {
            intro h11;
            have h12 := Fin.val_eq_of_eq h11;
            simp at h12;
            have h13: (↑x':Fin (n + 1)).val = x'.val := rfl;
            rw [h13] at h12;
            have h14 := x'.isLt;
            rw [h12] at h14;
            have h15 := Nat.lt_irrefl n;
            contradiction;
          };
          have h11 := prop_hpnFinr nFin prop_hpnFinl;
          rw [h11] at prop_hpnFinr;
          have h12: { val := x'.val, isLt := (_ : x'.val < Nat.succ n) : Fin (n + 1) } = x' := rfl;
          rw [←pn, h12] at h7;
          have h13 := Fin.eq_of_val_eq h7;
          have h14 := Eq.symm (prop_hpnFinr ↑x' h13);
          contradiction;
        };
      };
      case inr => {
        have h5 := prop_hpnFinr nFin prop_hpnFinl;
        have ⟨w, ⟨h6l, h6r⟩⟩ := h ↑y;
        have h7: w ≠ nFin := by {
          intro h8;
          rw [h8, pn] at h6l;
          exact absurd (Eq.symm h6l) h4;
        };
        exists downcast w h7;
        have h8 := coe_downcast w h7;
        apply And.intro;
        case left => {
          apply Fin.eq_of_val_eq;
          simp [h8];
          byCases h9: w = whnFin;
          rw [h9, prop_hnFinl] at h6l;
          have h10: n = y.val := by {
            have h11 := Fin.val_eq_of_eq h6l;
            simp at h11;
            assumption;
          };
          have h11: n ≠ y.val := by {
            have h12 := y.isLt;
            intro h13;
            have h14 := Nat.lt_irrefl n;
            rw [←h13] at h12;
            contradiction;
          };
          contradiction;
          simp [h9];
          have h13: { val := w.val, isLt := (_ : (downcast w h7).val < Nat.succ n) : Fin (n + 1)} = ↑(downcast w h7) := rfl;
          --rw [h13, h8];
          have h14 := Fin.val_eq_of_eq h6l;
          assumption;
        };
        case right => {
          intro x' h9;
          simp [h8] at h9;
          byCases h10: w = whnFin;
          all_goals byCases h11: ↑x' = whnFin;
          all_goals simp [h10, h11] at h9;
          apply Fin.eq_of_val_eq;
          simp;
          have h12 := Fin.val_eq_of_eq (Eq.trans h10 (Eq.symm h11));
          assumption;
          rw [←pn, ←prop_hpnFinl] at h9;
          have h12 := Fin.eq_of_val_eq h9;
          specialize prop_hpnFinr ↑x' h12;
          rw [h5] at prop_hpnFinr;
          have h13 := Fin.val_eq_of_eq prop_hpnFinr;
          simp at h13;
          have h14 := x'.isLt;
          have h15 := Nat.lt_irrefl n;
          have h16: (↑x':(Fin (n + 1))).val = x'.val := rfl;
          rw [←h16, ←h13] at h14;
          contradiction;
          rw [←pn, ←prop_hpnFinl] at h9;
          have h12 := Fin.eq_of_val_eq h9;
          specialize prop_hpnFinr ↑(downcast w h7) (Eq.symm h12);
          rw [h5, h8] at prop_hpnFinr;
          have h13 := Eq.symm prop_hpnFinr;
          contradiction;
          have h12: { val := w.val, isLt := (_ : (downcast w h7).val < Nat.succ n) : Fin (n + 1) } = ↑(downcast w h7) := rfl;
          have h13: { val := x'.val, isLt := (_ : x'.val < Nat.succ n) : Fin (n + 1) } = ↑x' := rfl;
          --rw [h12];
          rw [h13] at h9;
          specialize h6r ↑x' (Fin.eq_of_val_eq h9);
          apply Fin.eq_of_val_eq;
          simp;
          have h14 := Fin.val_eq_of_eq h6r;
          rw [h14];
          --rfl;
        };
      };
    };
  }⟩;
  byCases h1: nFin = p nFin;
  --恒等写像との合成になる場合
  case inl => {
    specialize prop_hnFinr nFin (Eq.trans prop_hnFinl h1);
    exists q;
    apply Or.intro_left;
    simp [Perm.id];
    --rw [←Bijection.rightIdentity];
    apply Subtype.eq;
    --simp [coe, CoeT.coe, CoeHTCT.coe, coeTC, CoeTC.coe, coeB, Coe.coe];
    --simp;
    apply funext;
    intro x;
    byCases h4: x = whnFin;
    case inl => {
      rw [h4];
      have h5: ¬whnFin < n := by {
        rw [prop_hnFinr];
        simp;
        exact Nat.lt_irrefl n;
      };
      simp [h5];
      exact Eq.trans prop_hnFinl (Eq.symm prop_hnFinr);
    };
    case inr => {
      rw [prop_hnFinr] at h4;
      have h5 := ltn x h4;
      simp [h5];
      rw [←Bijection.rightIdentity];
      apply Fin.eq_of_val_eq;
      simp;
      --generalize h6: { val := x.val, isLt := (_ : { val := x.val, isLt := (_ : x.val < n): Fin n}.val < Nat.succ n) : Fin (n + 1)} = x'';
      /-have h7: x'' = x := by {
        apply Fin.eq_of_val_eq;
        rw [←h6];
      };-/
      --rw [h7];
      have h4' : ¬x.val = n := by {
        intro aa;
        have bb : n = nFin.val := rfl;
        have cc := Fin.eq_of_val_eq (Eq.trans aa bb);
        contradiction;
      };
      simp [prop_hnFinr, h4'];
    };
  };
  --置換との合成になる場合
  case inr => {
    exists q;
    apply Or.intro_right;
    exists pnFin;
    let t: Transposition pnFin (Fin.ofNat n) :=
      let p': Perm (n + 1) :=
        ⟨λx => if x = pnFin then nFin else if x = nFin then pnFin else x, by {
          simp [bije];
          intro y;
          byCases h2: y = nFin;
          exists pnFin;
          simp;
          rw [h2];
          simp;
          intro x' h3;
          byCases h4: x' = pnFin;
          exact Eq.symm h4;
          simp [h4] at h3;
          byCases h5: x' = nFin;
          simp [h5] at h3;
          rw [pn] at h1;
          contradiction;
          simp [h5] at h3;
          rw [←h3] at h5;
          simp at h5;
          byCases h3: y = pnFin;
          exists nFin;
          simp [←pn, h1, h3];
          intro x' h4;
          byCases h5: x' = pnFin;
          simp [pn, h5] at h4;
          rw [pn, h4] at h1;
          exact absurd rfl h1;
          simp [pn, h5] at h4;
          byCases h6: x' = nFin;
          rw [h6];
          simp [h6] at h4;
          rw [h4] at h5;
          simp at h5;
          exists y;
          simp [h3, h2];
          intro x' h4;
          byCases h5: x' = pnFin;
          simp [h5] at h4;
          contradiction;
          simp [h5] at h4;
          byCases h6: x' = nFin;
          simp [h6] at h4;
          contradiction;
          simp [h6] at h4;
          assumption;
        }⟩;
      ⟨p' , by {
        have eq_nFin: (Fin.ofNat n) = nFin := by {
          apply Fin.eq_of_val_eq;
          simp [Fin.ofNat];
          apply Nat.mod_eq_of_lt;
          exact Nat.lt.base n;
        };
        rw [eq_nFin];
        apply And.intro;
        case left => {
          rw [pn] at h1;
          exact ltn pnFin (Ne.symm h1);
        };
        case right => {
          apply And.intro;
          simp;
          apply And.intro;
          rw [pn] at h1;
          simp [h1];
          intro k ⟨h2l, h2r⟩;
          simp [h2l, h2r];
        };
      }⟩;
    exists t;
    apply Subtype.eq;
    simp;
    apply funext;
    intro x;
    simp [HMul.hMul, Mul.mul, Bijection.comp];
    byCases h2: x = nFin;
    case inl => {
      simp [h2];
      have h3: (↑q:Perm (n + 1)).val nFin = nFin := by {
        apply Fin.eq_of_val_eq;
        simp;
        --simp [coe, CoeT.coe, CoeHTCT.coe, coeTC, CoeTC.coe, coeB, Coe.coe];
        have h3 := Nat.lt_irrefl n;
        simp [h3];
      };
      simp [h3];
      have h3' := Nat.lt_irrefl n;
      simp [h3'];
      rw [←pn];
      simp [h1];
    };
    case inr => {
      --simp [coe, CoeT.coe, CoeHTCT.coe, coeTC, CoeTC.coe, coeB, Coe.coe];
      have h3 := ltn x h2;
      simp [h3];
      byCases h4: x = whnFin;
      have h5: (↑q: Perm (n + 1)).val whnFin = pnFin := by {
        --simp [coe, CoeT.coe, CoeHTCT.coe, coeTC, CoeTC.coe, coeB, Coe.coe];
        have h6 := Fin.val_eq_of_eq h4;
        rw [h6] at h3;
        simp [h3];
        apply Fin.eq_of_val_eq;
        simp;
        /-
        have h7: ∀p, {val := whnFin.val, isLt := p} = whnFin := by {
          intro p;
          apply Fin.eq_of_val_eq;
          simp;
        };
        simp [h7];
        -/
      };
      have hoge : ∀p, {val := x.val, isLt := p} = x := by {
        intro p;
        apply Fin.eq_of_val_eq;
        simp;
      };
      simp [h4, h5];
      have fuga : ∀n p, {val := x.val, isLt := p : Fin n}.val = x.val := by {
        intros;
        simp;
      };
      have poyo : { val := x.val, isLt := (_ : { val := x.val, isLt := (_ : x.val < n) : Fin n}.val < Nat.succ n) : Fin (n + 1)} = whnFin := by {
        rw [←h4];
      };
      --assumption;
      simp [fuga, poyo];
      
      have h5: (↑q: Perm (n + 1)).val x = p x := by {
        --simp [coe, CoeT.coe, CoeHTCT.coe, coeTC, CoeTC.coe, coeB, Coe.coe];
        simp [h3];
        have h7: ∀p, {val := x.val, isLt := p} = x := by {
          intro p;
          apply Fin.eq_of_val_eq;
          simp;
        };
        apply Fin.eq_of_val_eq;
        simp [h7, h4];
        rw [prop_hnFinl];
      };
      rw [h5];
      have ⟨w, ⟨h6l, h6r⟩⟩ := bije_contraposition h pnFin;
      rw [←pn, ←prop_hpnFinl] at h6l;
      have h7 := prop_hpnFinr w (Eq.symm h6l);
      specialize prop_hpnFinr nFin prop_hpnFinl;
      rw [←prop_hpnFinr, h7] at h2;
      specialize h6r x (Ne.symm h2);
      rw [←h7, prop_hpnFinr] at h6r;
      have h8 := Ne.symm h6r;
      rw [←pn];
      simp [h8];
      have ⟨w', ⟨h9l, h9r⟩⟩ := bije_contraposition h nFin;
      rw [←h9l] at prop_hnFinl;
      have h10 := prop_hnFinr w' prop_hnFinl;
      rw [h10] at h4;
      specialize h9r x (Ne.symm h4);
      rw [←h9l];
      simp [(Ne.symm h9r)];
    };
  };
}