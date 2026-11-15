/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.Label
import Inkproof.Axis.Proofs.Grid

universe u

namespace Inkproof.Axis.Proofs

open Lean.Grind

/-- The number written by digits given least significant first. -/
def lsValue (ds : List Nat) : Nat := ds.foldr (fun d a => d + 10 * a) 0

private theorem cases_lt_ten {d : Nat} (h : d < 10) :
    d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega

theorem digitChar_isDigit {d : Nat} (h : d < 10) : (digitChar d).isDigit = true := by
  rcases cases_lt_ten h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem digitChar_toNat {d : Nat} (h : d < 10) : (digitChar d).toNat - 48 = d := by
  rcases cases_lt_ten h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem lsDigits_lt (m w : Nat) : ∀ d ∈ lsDigits m w, d < 10 := by
  induction w generalizing m with
  | zero => simp [lsDigits]
  | succ w ih =>
    intro d hd
    simp only [lsDigits, List.mem_cons] at hd
    rcases hd with rfl | hd
    · omega
    · exact ih _ d hd

theorem lsDigits_length (m w : Nat) : (lsDigits m w).length = w := by
  induction w generalizing m with
  | zero => simp [lsDigits]
  | succ w ih => simp [lsDigits, ih]

private theorem list_strong {α : Type u} {P : List α → Prop}
    (h : ∀ l, (∀ l', l'.length < l.length → P l') → P l) (l : List α) : P l := by
  have : ∀ n, ∀ l : List α, l.length = n → P l := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih => intro l hl; exact h l (fun l' h' => ih _ (hl ▸ h') l' rfl)
  exact this _ l rfl

theorem lsValue_lsDigits (m w : Nat) : lsValue (lsDigits m w) = m % 10 ^ w := by
  induction w generalizing m with
  | zero => simp [lsDigits, lsValue, Nat.mod_one]
  | succ w ih =>
    have := ih (m / 10)
    simp only [lsValue] at this
    simp only [lsDigits, lsValue, List.foldr_cons, this]
    rw [Nat.pow_succ, Nat.mul_comm (10 ^ w) 10, Nat.mod_mul]

theorem lt_pow_digitCount (m : Nat) : m < 10 ^ digitCount m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    unfold digitCount
    split
    · simpa using ‹m < 10›
    · have := ih (m / 10) (by omega)
      rw [Nat.pow_succ]
      omega

theorem digitCount_spec (m : Nat) : m < 10 ^ digitCount m ∧ (m < 10 ∨ 10 ^ (digitCount m - 1) ≤ m) := by
  refine ⟨lt_pow_digitCount m, ?_⟩
  induction m using Nat.strongRecOn with
  | _ m ih =>
    by_cases h : m < 10
    · exact Or.inl h
    · right
      have h1 : digitCount m = digitCount (m / 10) + 1 := by rw [digitCount]; simp [h]
      rw [h1, Nat.add_sub_cancel]
      rcases ih (m / 10) (by omega) with h2 | h2
      · have : digitCount (m / 10) = 1 := by rw [digitCount]; simp [h2]
        rw [this]; omega
      · have : 10 ^ (digitCount (m / 10) - 1) * 10 ≤ m := by omega
        have h3 : 0 < digitCount (m / 10) := by rw [digitCount]; split <;> omega
        calc 10 ^ digitCount (m / 10) = 10 ^ (digitCount (m / 10) - 1) * 10 := by
              rw [← Nat.pow_succ]; congr 1; omega
          _ ≤ m := this

theorem groupRuns_of_le (g : Char) (k : Nat) (l : List Char) (h : l.length ≤ k) : groupRuns g k l = l := by
  rw [groupRuns]; split
  · omega
  · rfl

theorem groupRuns_of_lt (g : Char) (k : Nat) (hk : 0 < k) (l : List Char) (h : k < l.length) :
    groupRuns g k l = l.take k ++ g :: groupRuns g k (l.drop k) := by
  rw [groupRuns]; simp [hk, h]

theorem length_groupRuns (g : Char) (k : Nat) (hk : 0 < k) (l : List Char) :
    (groupRuns g k l).length = l.length + (l.length - 1) / k := by
  induction l using list_strong with
  | _ l ih =>
    by_cases h : k < l.length
    · rw [groupRuns_of_lt g k hk l h]
      have := ih (l.drop k) (by simp; omega)
      simp only [List.length_append, List.length_cons, List.length_take, List.length_drop] at this ⊢
      rw [this]
      have e : (l.length - 1) / k = (l.length - k - 1) / k + 1 := by
        rw [show l.length - 1 = (l.length - k - 1) + k * 1 by omega, Nat.add_mul_div_left _ _ hk]
      rw [e]; omega
    · rw [groupRuns_of_le g k l (by omega)]
      have : (l.length - 1) / k = 0 := Nat.div_eq_of_lt (by omega)
      omega

theorem digitsValue_reverse (ds : List Nat) (h : ∀ d ∈ ds, d < 10) :
    digitsValue (ds.reverse.map digitChar) = lsValue ds := by
  induction ds with
  | nil => simp [digitsValue, lsValue]
  | cons d ds ih =>
    have hd : d < 10 := h d (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, digitsValue,
      List.foldl_append, List.foldl_cons, List.foldl_nil, digitChar_toNat hd] at *
    simp only [lsValue, List.foldr_cons] at *
    rw [this]; omega

theorem filter_groupRuns (g : Char) (k : Nat) (hk : 0 < k) (l : List Char) (hg : g ∉ l) :
    (groupRuns g k l).filter (· ≠ g) = l := by
  induction l using list_strong with
  | _ l ih =>
    unfold groupRuns
    split
    · rename_i h
      have hg1 : g ∉ l.take k := fun hm => hg (List.mem_of_mem_take hm)
      have hg2 : g ∉ l.drop k := fun hm => hg (List.mem_of_mem_drop hm)
      rw [List.filter_append, List.filter_cons, ih _ (by simp; omega) hg2]
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
      rw [List.filter_eq_self.2 (fun x hx => by simp; rintro rfl; exact hg1 hx)]
      exact List.take_append_drop k l
    · exact List.filter_eq_self.2 (fun x hx => by simp; rintro rfl; exact hg hx)

private theorem mem_groupRuns (g : Char) (k : Nat) (l : List Char) {x : Char} (hx : x ∈ groupRuns g k l) :
    x = g ∨ x ∈ l := by
  induction l using list_strong with
  | _ l ih =>
    unfold groupRuns at hx
    split at hx
    · simp only [List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | hx
      · exact Or.inr (List.mem_of_mem_take hx)
      · exact Or.inl rfl
      · rcases ih _ (by simp; omega) hx with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_of_mem_drop h)
    · exact Or.inr hx

theorem splitAtChar_none (c : Char) (a : List Char) (h : c ∉ a) : splitAtChar c a = (a, none) := by
  induction a with
  | nil => simp [splitAtChar]
  | cons x r ih =>
    have hx : x ≠ c := fun e => h (e ▸ List.mem_cons_self)
    simp [splitAtChar, hx, ih (fun m => h (List.mem_cons_of_mem _ m))]

theorem splitAtChar_some (c : Char) (a b : List Char) (h : c ∉ a) :
    splitAtChar c (a ++ c :: b) = (a, some b) := by
  induction a with
  | nil => simp [splitAtChar]
  | cons x r ih =>
    have hx : x ≠ c := fun e => h (e ▸ List.mem_cons_self)
    simp [splitAtChar, hx, ih (fun m => h (List.mem_cons_of_mem _ m))]

theorem ungroup_group {loc : Locale} (hl : loc.Valid) (l : List Char)
    (hd : ∀ c ∈ l, c.isDigit = true) : ungroupWhole loc (groupWhole loc l) = l := by
  unfold ungroupWhole groupWhole
  cases hg : loc.group with
  | none => rfl
  | some g =>
    obtain ⟨h1, _, _, h3⟩ := hl.2.2 g hg
    exact filter_groupRuns g _ h3 l (fun m => by have := hd g m; simp_all)

private theorem decimal_notMem_group {loc : Locale} (hl : loc.Valid) (l : List Char)
    (hd : ∀ c ∈ l, c.isDigit = true) : loc.decimal ∉ groupWhole loc l := by
  intro hm
  unfold groupWhole at hm
  cases hg : loc.group with
  | none =>
    rw [hg] at hm
    have := hd _ hm
    exact hl.1 (by simpa using this)
  | some g =>
    rw [hg] at hm
    obtain ⟨_, h2, _, _⟩ := hl.2.2 g hg
    rcases mem_groupRuns g _ l hm with h | h
    · exact h2 h.symm
    · exact hl.1 (hd _ h)

private theorem filter_reverse' {α : Type u} (p : α → Bool) (l : List α) :
    (l.reverse).filter p = (l.filter p).reverse := List.filter_reverse

/-- A label reads back as the mantissa and decimals it was written from. -/
theorem parseChars_formatChars {loc : Locale} (hl : loc.Valid) (p : Nat) (n : Int) :
    parseChars loc (formatChars loc p n) = some (n, p) := by
  have hW : p < max (digitCount n.natAbs) (p + 1) := by omega
  have hm : n.natAbs < 10 ^ max (digitCount n.natAbs) (p + 1) :=
    Nat.lt_of_lt_of_le (lt_pow_digitCount _) (Nat.pow_le_pow_right (by omega) (by omega))
  generalize hW' : max (digitCount n.natAbs) (p + 1) = W at hW hm
  have hlt := lsDigits_lt n.natAbs W
  have hlen := lsDigits_length n.natAbs W
  generalize hds : lsDigits n.natAbs W = ds at hlt hlen
  have hval : lsValue ds = n.natAbs := by
    rw [← hds, lsValue_lsDigits]; exact Nat.mod_eq_of_lt hm
  have hwd : ∀ c ∈ (ds.drop p).map digitChar, c.isDigit = true := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    exact digitChar_isDigit (hlt d (List.mem_of_mem_drop hd))
  have hfd : ∀ c ∈ (ds.take p).map digitChar, c.isDigit = true := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    exact digitChar_isDigit (hlt d (List.mem_of_mem_take hd))
  have hne : (ds.drop p).map digitChar ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this; omega
  have hung := ungroup_group hl _ hwd
  have hdec := decimal_notMem_group hl _ hwd
  have hlen' : ((ds.take p).map digitChar).length = p := by simp; omega
  have hall : ∀ c ∈ ((ds.drop p).map digitChar).reverse ++ ((ds.take p).map digitChar).reverse,
      c.isDigit = true := by
    intro c hc
    simp only [List.mem_append, List.mem_reverse] at hc
    rcases hc with hc | hc
    · exact hwd c hc
    · exact hfd c hc
  have hjoin : (((ds.drop p).map digitChar).reverse ++ ((ds.take p).map digitChar).reverse) =
      ds.reverse.map digitChar := by
    rw [← List.map_reverse, ← List.map_reverse, ← List.map_append, ← List.reverse_append,
      List.take_append_drop]
  have hv := digitsValue_reverse ds hlt
  have hsplit : splitAtChar loc.decimal
      ((groupWhole loc ((ds.drop p).map digitChar)).reverse ++
        (if p = 0 then [] else loc.decimal :: ((ds.take p).map digitChar).reverse)) =
      ((groupWhole loc ((ds.drop p).map digitChar)).reverse,
        if p = 0 then none else some ((ds.take p).map digitChar).reverse) := by
    split
    · rw [List.append_nil]; exact splitAtChar_none _ _ (fun m => hdec (List.mem_reverse.1 m))
    · exact splitAtChar_some _ _ _ (fun m => hdec (List.mem_reverse.1 m))
  have hungr : ungroupWhole loc (groupWhole loc ((ds.drop p).map digitChar)).reverse =
      ((ds.drop p).map digitChar).reverse := by
    have := congrArg List.reverse hung
    unfold ungroupWhole at *
    cases hg : loc.group with
    | none => simp only [hg] at this ⊢; simpa using this
    | some g => simp only [hg] at this ⊢; rw [List.filter_reverse]; simpa using this
  have hwrne : (groupWhole loc ((ds.drop p).map digitChar)).reverse ≠ [] := by
    intro h
    rw [h] at hungr
    have e : ungroupWhole loc [] = [] := by unfold ungroupWhole; cases loc.group <;> simp
    rw [e] at hungr
    exact hne (List.reverse_eq_nil_iff.1 hungr.symm)
  have hminus : loc.minus ∉ (groupWhole loc ((ds.drop p).map digitChar)).reverse := by
    intro hm
    rw [List.mem_reverse] at hm
    unfold groupWhole at hm
    cases hg : loc.group with
    | none => rw [hg] at hm; exact hl.2.1 (by simpa using hwd _ hm)
    | some g =>
      rw [hg] at hm
      obtain ⟨_, _, h3, _⟩ := hl.2.2 g hg
      rcases mem_groupRuns g _ _ hm with h | h
      · exact h3 h.symm
      · exact hl.2.1 (hwd _ h)
  have hfmt : formatChars loc p n = (if n < 0 then [loc.minus] else []) ++
      ((groupWhole loc ((ds.drop p).map digitChar)).reverse ++
        (if p = 0 then [] else loc.decimal :: ((ds.take p).map digitChar).reverse)) := by
    rw [← hds]; simp only [formatChars, hW', List.append_assoc]
  rw [hfmt]
  have hres : ∀ neg : Bool, (neg = true → n < 0) → (neg = false → 0 ≤ n) →
      (let (whole, frac) := splitAtChar loc.decimal
          ((groupWhole loc ((ds.drop p).map digitChar)).reverse ++
            (if p = 0 then [] else loc.decimal :: ((ds.take p).map digitChar).reverse))
        let whole := ungroupWhole loc whole
        let frac := frac.getD []
        if !whole.isEmpty && (whole ++ frac).all Char.isDigit then
          let v : Int := digitsValue (whole ++ frac)
          some (if neg then -v else v, frac.length)
        else none) = some (n, p) := by
    intro neg h1 h2
    rw [hsplit]
    simp only []
    rw [hungr]
    have hfr : (if p = 0 then (none : Option (List Char)) else some ((ds.take p).map digitChar).reverse).getD [] =
        ((ds.take p).map digitChar).reverse := by
      split
      · rename_i h0; subst h0; simp at hlen'; simp
      · rfl
    rw [hfr, hjoin]
    have hall' : ((ds.reverse.map digitChar)).all Char.isDigit = true := by
      rw [← hjoin]; exact List.all_eq_true.2 hall
    have hne' : ((ds.drop p).map digitChar).reverse.isEmpty = false := by
      cases h : ((ds.drop p).map digitChar).reverse <;> simp_all
    simp only [hne', hall', Bool.not_false, Bool.true_and, hv, hval]
    simp only [List.length_reverse, hlen']
    have : (if neg = true then -((n.natAbs : Nat) : Int) else ((n.natAbs : Nat) : Int)) = n := by
      cases neg
      · have := h2 rfl; simp; omega
      · have := h1 rfl; simp; omega
    simp [this]
  unfold parseChars
  by_cases hn : n < 0
  · simp only [hn, ite_true, List.cons_append]
    exact hres true (fun _ => hn) (by simp)
  · obtain ⟨c, r, hcr⟩ := List.exists_cons_of_ne_nil hwrne
    have hc : c ≠ loc.minus := fun e => hminus (e ▸ hcr ▸ List.mem_cons_self)
    simp only [hn, ite_false, List.nil_append, hcr, List.cons_append, hc]
    rw [← List.cons_append, ← hcr]
    exact hres false (by simp) (fun _ => by omega)

/-- A label reads back as the tick rounded to the displayed precision. -/
theorem parse_label {loc : Locale} (hl : loc.Valid) {α : Type u} [IntCast α] [NatCast α] [Mul α] [Add α] [Div α]
    (fl : α → Int) (p : Nat) (x : α) : parseChars loc (label loc fl p x).toList = some (scaled fl p x, p) := by
  simp [label, parseChars_formatChars hl]

section
attribute [local instance] Ring.intCast Semiring.natCast

variable {α : Type u} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

theorem scaled_succ {fl : α → Int} (hfl : IsFloor fl) (p : Nat) {x s : α}
    (hs : 1 ≤ s * ((10 ^ p : Nat) : α)) : scaled fl p x + 1 ≤ scaled fl p (x + s) := by
  unfold scaled
  generalize hy : x * ((10 ^ p : Nat) : α) + ((1 : Int) : α) / ((2 : Int) : α) = y
  have h : (x + s) * ((10 ^ p : Nat) : α) + ((1 : Int) : α) / ((2 : Int) : α) = y + s * ((10 ^ p : Nat) : α) := by
    rw [← hy]; grind
  rw [h]
  by_cases hc : fl y + 1 ≤ fl (y + s * ((10 ^ p : Nat) : α))
  · exact hc
  · exfalso
    have h1 : fl (y + s * ((10 ^ p : Nat) : α)) ≤ fl y := by omega
    have h2 := intCast_le (α := α) h1
    have h3 := (hfl y).1
    have h4 := (hfl (y + s * ((10 ^ p : Nat) : α))).2
    grind

/-- On a grid whose step is at least one unit of the displayed precision, adjacent labels differ. -/
theorem label_adjacent_ne {loc : Locale} (hl : loc.Valid) {fl : α → Int} (hfl : IsFloor fl) (g : Grid α) (p : Nat)
    (hs : 1 ≤ g.step * ((10 ^ p : Nat) : α)) (i : Nat) :
    label loc fl p (g.value i) ≠ label loc fl p (g.value (i + 1)) := by
  intro h
  have h1 := parse_label hl fl p (g.value i)
  have h2 := parse_label hl fl p (g.value (i + 1))
  rw [h, h2] at h1
  have h3 : g.value (i + 1) = g.value i + g.step := by have := value_succ_sub g i; grind
  have h4 := scaled_succ hfl p (x := g.value i) hs
  rw [← h3] at h4
  have : scaled fl p (g.value (i + 1)) = scaled fl p (g.value i) := by simpa using h1
  omega

omit [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] in
/-- `scaled` is the floor of `x` in units of `10 ^ -p`, after adding half a unit. -/
theorem scaled_spec {fl : α → Int} (hfl : IsFloor fl) (p : Nat) (x : α) :
    (Int.cast (scaled fl p x) : α) ≤ x * ((10 ^ p : Nat) : α) + ((1 : Int) : α) / ((2 : Int) : α) ∧
      x * ((10 ^ p : Nat) : α) + ((1 : Int) : α) / ((2 : Int) : α) < Int.cast (scaled fl p x) + 1 :=
  hfl _

end

theorem ungroupWhole_spec (loc : Locale) (l : List Char) :
    ungroupWhole loc l = match loc.group with | some g => l.filter (· ≠ g) | none => l := rfl

theorem groupWhole_spec (loc : Locale) (l : List Char) :
    groupWhole loc l = match loc.group with | some g => groupRuns g loc.groupSize l | none => l := rfl

end Inkproof.Axis.Proofs