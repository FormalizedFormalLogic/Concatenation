module

public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Logic.Relation

/-!
# Atomic pairings

Binary operations that are free pairings outside a multiplication table of atoms, and the
back-and-forth between two of them with the same table.
-/

@[expose] public section

namespace AtomicPairing

/-- `y` is a left or a right factor of `x`. -/
def IsFactor {M : Type*} [Append M] (y x : M) : Prop := ∃ z, x = y ++ z ∨ x = z ++ y

end AtomicPairing

/--
An operation `++` with atoms named by `S` whose products are again atoms exactly as the table `tbl`
says, and which is otherwise an injective pairing onto the elements that are not atoms, without
cycles.
-/
structure AtomicPairing {S : Type*} (tbl : S → S → S → Prop) (M : Type*) [Append M] where
  /-- The atom of a name. -/
  atom : S → M
  atom_injective : Function.Injective atom
  atom_append_atom (s s' s'' : S) : atom s ++ atom s' = atom s'' ↔ tbl s s' s''
  exists_atom_of_append {x y : M} {s : S} :
    x ++ y = atom s → (∃ s', x = atom s') ∧ ∃ s', y = atom s'
  append_injective {x y x' y' : M} :
    (∀ s, x ++ y ≠ atom s) → x ++ y = x' ++ y' → x = x' ∧ y = y'
  exists_append {x : M} : (∀ s, x ≠ atom s) → ∃ y z, x = y ++ z
  exists_ne_atom : ∃ x, ∀ s, x ≠ atom s
  acyclic (x : M) : ¬Relation.TransGen AtomicPairing.IsFactor x x

namespace AtomicPairing

variable {S : Type*} {tbl : S → S → S → Prop} {M M' : Type*} [Append M] [Append M']

section

variable (F : AtomicPairing tbl M) {x y z : M} {i : Bool} {p q : List Bool} {n : ℕ}

/-- `x` is an atom. -/
def IsAtom (x : M) : Prop := ∃ s, x = F.atom s

open Classical in
/-- The left factor of an element that is not an atom, and the element itself for an atom. -/
noncomputable def left (x : M) : M :=
  if h : F.IsAtom x then x else (F.exists_append (not_exists.mp h)).choose

open Classical in
/-- The right factor of an element that is not an atom, and the element itself for an atom. -/
noncomputable def right (x : M) : M :=
  if h : F.IsAtom x then x else (F.exists_append (not_exists.mp h)).choose_spec.choose

lemma left_of_isAtom (h : F.IsAtom x) : F.left x = x := by simp [left, h]

lemma right_of_isAtom (h : F.IsAtom x) : F.right x = x := by simp [right, h]

lemma left_append_right (h : ¬F.IsAtom x) : F.left x ++ F.right x = x := by
  simp only [left, right, h, ↓reduceDIte]
  exact (F.exists_append (not_exists.mp h)).choose_spec.choose_spec.symm

lemma left_append (h : ¬F.IsAtom (y ++ z)) : F.left (y ++ z) = y :=
  (F.append_injective (not_exists.mp h) (F.left_append_right h).symm).1.symm

lemma right_append (h : ¬F.IsAtom (y ++ z)) : F.right (y ++ z) = z :=
  (F.append_injective (not_exists.mp h) (F.left_append_right h).symm).2.symm

lemma isFactor_left (h : ¬F.IsAtom x) : IsFactor (F.left x) x :=
  ⟨F.right x, .inl (F.left_append_right h).symm⟩

lemma isFactor_right (h : ¬F.IsAtom x) : IsFactor (F.right x) x :=
  ⟨F.left x, .inr (F.left_append_right h).symm⟩

/-- The right factor for `true` and the left factor for `false`. -/
noncomputable def child (i : Bool) (x : M) : M := bif i then F.right x else F.left x

@[simp]
lemma child_false : F.child false x = F.left x := rfl

@[simp]
lemma child_true : F.child true x = F.right x := rfl

lemma child_of_isAtom (h : F.IsAtom x) : F.child i x = x := by
  cases i <;> simp [F.left_of_isAtom h, F.right_of_isAtom h]

/-- The component of `x` along the path `p` of left and right factors. -/
noncomputable def comp (p : List Bool) (x : M) : M := p.foldl (fun x i ↦ F.child i x) x

@[simp]
lemma comp_nil : F.comp [] x = x := rfl

@[simp]
lemma comp_cons : F.comp (i :: p) x = F.comp p (F.child i x) := rfl

@[simp]
lemma comp_append : F.comp (p ++ q) x = F.comp q (F.comp p x) := List.foldl_append ..

lemma comp_of_isAtom (h : F.IsAtom x) : F.comp p x = x := by
  induction p with
  | nil => rfl
  | cons i p ih => rw [comp_cons, F.child_of_isAtom h, ih]

/-- The elements `e`, `e ++ e`, `(e ++ e) ++ (e ++ e)`, … for an element `e` that is not an atom. -/
noncomputable def tower : ℕ → M
  | 0 => F.exists_ne_atom.choose
  | n + 1 => tower n ++ tower n

@[simp]
lemma tower_succ : F.tower (n + 1) = F.tower n ++ F.tower n := rfl

lemma not_isAtom_tower (n : ℕ) : ¬F.IsAtom (F.tower n) := by
  induction n with
  | zero => exact not_exists.mpr F.exists_ne_atom.choose_spec
  | succ n ih =>
    rintro ⟨s, hs⟩
    exact ih (F.exists_atom_of_append hs).1

lemma tower_injective : Function.Injective F.tower := by
  have h {i j : ℕ} (hij : i < j) : Relation.TransGen IsFactor (F.tower i) (F.tower j) := by
    induction j, hij using Nat.le_induction with
    | base => exact .single ⟨F.tower i, .inl rfl⟩
    | succ j _ ih => exact ih.tail ⟨F.tower j, .inl rfl⟩
  intro i j hij
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt <;> exact F.acyclic _ (hij ▸ h hlt)

variable (T : Set M)

/-- Every descent from `x` through left and right factors leaves `T` within `n` steps. -/
def HeightLE : ℕ → M → Prop
  | 0, x => x ∉ T
  | n + 1, x => x ∉ T ∨ (HeightLE n (F.left x) ∧ HeightLE n (F.right x))

variable {T}

lemma heightLE_of_notMem (h : x ∉ T) : ∀ n, F.HeightLE T n x
  | 0 => h
  | _ + 1 => .inl h

lemma heightLE_induction {P : ℕ → M → Prop} (h₀ : ∀ n x, x ∉ T → P n x)
    (h₁ : ∀ n x, x ∈ T → P n (F.left x) → P n (F.right x) → P (n + 1) x) :
    ∀ n x, F.HeightLE T n x → P n x := by
  intro n
  induction n with
  | zero => exact fun x h ↦ h₀ 0 x h
  | succ n ih =>
    rintro x (h | ⟨hl, hr⟩)
    · exact h₀ _ x h
    · by_cases hx : x ∈ T
      · exact h₁ n x hx (ih _ hl) (ih _ hr)
      · exact h₀ _ x hx

lemma heightLE_length (hT : ∀ x ∈ T, ¬F.IsAtom x) (L : List M) (x : M)
    (hx : ∀ y, Relation.ReflTransGen IsFactor y x → y ∈ T → y ∈ L) : F.HeightLE T L.length x := by
  classical
  suffices ∀ n (L : List M), L.length = n → ∀ x,
      (∀ y, Relation.ReflTransGen IsFactor y x → y ∈ T → y ∈ L) → F.HeightLE T n x from
    this _ L rfl x hx
  intro n
  induction n with
  | zero =>
    intro L hL x hx hxT
    simpa [List.length_eq_zero_iff.mp hL] using hx x .refl hxT
  | succ n ih =>
    intro L hL x hx
    by_cases hxT : x ∈ T
    · have hxL : x ∈ L := hx x .refl hxT
      have key (c : M) (hc : IsFactor c x) : F.HeightLE T n c := by
        apply ih (L.erase x) (by rw [List.length_erase_of_mem hxL, hL]; rfl)
        intro y hy hyT
        apply (List.mem_erase_of_ne _).mpr (hx y (hy.tail hc) hyT)
        rintro rfl
        exact F.acyclic _ (Relation.TransGen.tail' hy hc)
      exact .inr ⟨key _ (F.isFactor_left (hT x hxT)), key _ (F.isFactor_right (hT x hxT))⟩
    · exact F.heightLE_of_notMem hxT _

omit [Append M] in
/-- For finitely many elements, some level above `d` of a growing family of sets is a gap. -/
lemma exists_gap (A : ℕ → Set M) (hA : Monotone A) (L : List M) (d : ℕ) :
    ∃ θ, d ≤ θ ∧ θ < d + 2 ^ L.length ∧ ∀ x ∈ L, x ∈ A (θ + 1) → x ∈ A θ := by
  induction L generalizing d with
  | nil => exact ⟨d, le_rfl, by simp, by simp⟩
  | cons x L ih =>
    obtain ⟨θ, h₁, h₂, h₃⟩ := ih d
    simp only [List.length_cons, pow_succ, List.mem_cons, forall_eq_or_imp]
    by_cases hx : x ∈ A (θ + 1) → x ∈ A θ
    · exact ⟨θ, h₁, by omega, hx, h₃⟩
    · obtain ⟨θ', h₁', h₂', h₃'⟩ := ih (θ + 1)
      have hx : x ∈ A (θ + 1) := (not_imp.mp hx).1
      exact ⟨θ', by omega, by omega, fun _ ↦ hA h₁' hx, h₃'⟩

variable (T)

open Classical in
/--
The map that is `φ` outside `T` and sends an element of `T` to the product of the images of its
factors, cut off after `n` descents.
-/
noncomputable def build (φ : M → M') : ℕ → M → M'
  | 0, x => φ x
  | n + 1, x => if x ∈ T then build φ n (F.left x) ++ build φ n (F.right x) else φ x

variable {T}

lemma build_eq {φ : M → M'} (h : F.HeightLE T n x) (m : ℕ) (hm : n ≤ m) :
    F.build T φ m x = F.build T φ n x := by
  induction n generalizing x m with
  | zero =>
    have h : x ∉ T := h
    cases m <;> simp [build, h]
  | succ n ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rcases h with h | ⟨hl, hr⟩
    · simp [build, h]
    · by_cases hx : x ∈ T
      · simp [build, hx, ih hl m (by omega), ih hr m (by omega)]
      · simp [build, hx]

/--
A map that is `φ` outside a finite set `T` of elements that are not atoms, and sends an element of
`T` to the product of the images of its factors.
-/
lemma exists_copy (hT : ∀ x ∈ T, ¬F.IsAtom x) (L : List M) (hL : ∀ x ∈ T, x ∈ L) (φ : M → M') :
    ∃ H : M → M', (∀ x, x ∉ T → H x = φ x) ∧ (∀ x ∈ T, H x = H (F.left x) ++ H (F.right x)) ∧
      ∀ x, F.HeightLE T L.length x := by
  have hh (x : M) : F.HeightLE T L.length x := F.heightLE_length hT L x fun y _ hy ↦ hL y hy
  use F.build T φ L.length
  and_intros
  · intro x hx
    cases L.length <;> simp [build, hx]
  · intro x hx
    rw [← F.build_eq (hh x) (L.length + 1) (by omega)]
    simp [build, hx]
  · exact hh

end

section

variable (F : AtomicPairing tbl M) (F' : AtomicPairing tbl M') {ρ ρ' : Set (M × M')}
  {R R' : Set (M × M')} {a a' x : M} {b b' y : M'} {d d' : ℕ} {p : List Bool}

/-- The pairs of components, along the same path of length at most `d`, of the pairs in `ρ`. -/
def Reach (d : ℕ) (ρ : Set (M × M')) : Set (M × M') :=
  {z | ∃ a b p, (a, b) ∈ ρ ∧ List.length p ≤ d ∧ z = (F.comp p a, F'.comp p b)}

variable {F F'}

lemma mem_reach (h : (a, b) ∈ ρ) (hp : p.length ≤ d) :
    (F.comp p a, F'.comp p b) ∈ F.Reach F' d ρ := ⟨a, b, p, h, hp, rfl⟩

lemma reach_mono (hd : d ≤ d') (hρ : ρ ⊆ ρ') : F.Reach F' d ρ ⊆ F.Reach F' d' ρ' := by
  rintro _ ⟨a, b, p, h, hp, rfl⟩
  exact ⟨a, b, p, hρ h, hp.trans hd, rfl⟩

lemma child_mem_reach (h : (x, y) ∈ F.Reach F' d ρ) (i : Bool) :
    (F.child i x, F'.child i y) ∈ F.Reach F' (d + 1) ρ := by
  obtain ⟨a, b, p, hab, hp, h⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  exact ⟨a, b, p ++ [i], hab, by simpa using hp, by simp⟩

lemma reach_insert : F.Reach F' d (insert (a, b) ρ) =
    F.Reach F' d ρ ∪ {z | ∃ p : List Bool, p.length ≤ d ∧ z = (F.comp p a, F'.comp p b)} := by
  ext z
  constructor
  · rintro ⟨a', b', p, h | h, hp, rfl⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact .inr ⟨p, hp, rfl⟩
    · exact .inl ⟨a', b', p, h, hp, rfl⟩
  · rintro (h | ⟨p, hp, rfl⟩)
    · exact reach_mono le_rfl (Set.subset_insert _ _) h
    · exact mem_reach (Set.mem_insert _ _) hp

lemma reach_swap : F'.Reach F d (Prod.swap '' ρ) = Prod.swap '' F.Reach F' d ρ := by
  ext ⟨y, x⟩
  constructor
  · rintro ⟨_, _, p, ⟨⟨a, b⟩, h, e⟩, hp, h'⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact ⟨_, mem_reach h hp, h'.symm⟩
  · rintro ⟨_, ⟨a, b, p, h, hp, rfl⟩, h'⟩
    exact ⟨b, a, p, ⟨(a, b), h, rfl⟩, hp, h'.symm⟩

lemma finite_reach (hρ : ρ.Finite) : (F.Reach F' d ρ).Finite := by
  have h := (Set.Finite.prod hρ (List.finite_length_le Bool d)).image
    fun z : (M × M') × List Bool ↦ (F.comp z.2 z.1.1, F'.comp z.2 z.1.2)
  apply h.subset
  rintro _ ⟨a, b, p, h, hp, rfl⟩
  exact ⟨((a, b), p), ⟨h, hp⟩, rfl⟩

variable (F F')

/-- The relation `R` preserves equality and the names of atoms. -/
structure IsPartialIso (R : Set (M × M')) : Prop where
  eq_iff {x x' : M} {y y' : M'} : (x, y) ∈ R → (x', y') ∈ R → (x = x' ↔ y = y')
  atom_iff {x : M} {y : M'} : (x, y) ∈ R → ∀ s, x = F.atom s ↔ y = F'.atom s

variable {F F'}

namespace IsPartialIso

lemma mono (h : F.IsPartialIso F' R) (hR : R' ⊆ R) : F.IsPartialIso F' R' where
  eq_iff h₁ h₂ := h.eq_iff (hR h₁) (hR h₂)
  atom_iff h₁ := h.atom_iff (hR h₁)

lemma isAtom_iff (h : F.IsPartialIso F' R) (hxy : (x, y) ∈ R) : F.IsAtom x ↔ F'.IsAtom y :=
  exists_congr (h.atom_iff hxy)

lemma swap (h : F.IsPartialIso F' R) : F'.IsPartialIso F (Prod.swap '' R) where
  eq_iff := by
    rintro _ _ _ _ ⟨⟨x, y⟩, h₁, e⟩ ⟨⟨x', y'⟩, h₂, e'⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
    exact (h.eq_iff h₁ h₂).symm
  atom_iff := by
    rintro _ _ ⟨⟨x, y⟩, h₁, e⟩ s
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact (h.atom_iff h₁ s).symm

lemma insert (h : F.IsPartialIso F' R) (h₁ : ∀ x y, (x, y) ∈ R → (x = a ↔ y = b))
    (h₂ : ∀ s, a = F.atom s ↔ b = F'.atom s) : F.IsPartialIso F' (insert (a, b) R) where
  eq_iff := by
    rintro x y x' y' (e | hxy) (e' | hxy')
    · cases e; cases e'; simp
    · cases e; rw [eq_comm, h₁ _ _ hxy', eq_comm]
    · cases e'; exact h₁ _ _ hxy
    · exact h.eq_iff hxy hxy'
  atom_iff := by
    rintro x y (e | hxy) s
    · cases e; exact h₂ s
    · exact h.atom_iff hxy s

end IsPartialIso

variable (F F')

/-- The components up to depth `d` of the pairs in `ρ` correspond. -/
def Similar (d : ℕ) (ρ : Set (M × M')) : Prop := F.IsPartialIso F' (F.Reach F' d ρ)

variable {F F'}

lemma similar_empty (d : ℕ) : F.Similar F' d ∅ where
  eq_iff := by rintro _ _ _ _ ⟨_, _, _, h, -⟩; exact h.elim
  atom_iff := by rintro _ _ ⟨_, _, _, h, -⟩; exact h.elim

namespace Similar

lemma mono (h : F.Similar F' d' ρ') (hd : d ≤ d') (hρ : ρ ⊆ ρ') : F.Similar F' d ρ :=
  IsPartialIso.mono h (reach_mono hd hρ)

lemma swap (h : F.Similar F' d ρ) : F'.Similar F d (Prod.swap '' ρ) := by
  rw [Similar, reach_swap]
  exact IsPartialIso.swap h

lemma eq_iff (h : F.Similar F' d ρ) (hab : (a, b) ∈ ρ) (hab' : (a', b') ∈ ρ) : a = a' ↔ b = b' :=
  IsPartialIso.eq_iff h (mem_reach (p := []) hab (Nat.zero_le d))
    (mem_reach (p := []) hab' (Nat.zero_le d))

lemma insert_atom (h : F.Similar F' d ρ) (s : S) :
    F.Similar F' d (insert (F.atom s, F'.atom s) ρ) := by
  have h' : F.IsPartialIso F' (insert (F.atom s, F'.atom s) (F.Reach F' d ρ)) :=
    IsPartialIso.insert h (fun _ _ hxy ↦ IsPartialIso.atom_iff h hxy s) fun s' ↦ by
      rw [F.atom_injective.eq_iff, F'.atom_injective.eq_iff]
  apply h'.mono
  rw [reach_insert]
  rintro z (hz | ⟨p, -, rfl⟩)
  · exact .inr hz
  · rw [F.comp_of_isAtom ⟨s, rfl⟩, F'.comp_of_isAtom ⟨s, rfl⟩]
    exact .inl rfl

lemma append_eq_atom (h : F.Similar F' d ρ) (hab : (a, b) ∈ ρ) (hab' : (a', b') ∈ ρ) {s : S}
    (hs : a ++ a' = F.atom s) : b ++ b' = F'.atom s := by
  obtain ⟨⟨s₁, h₁⟩, s₂, h₂⟩ := F.exists_atom_of_append hs
  have ht : tbl s₁ s₂ s := (F.atom_append_atom _ _ _).mp (by rw [← h₁, ← h₂, hs])
  have hb : b = F'.atom s₁ :=
    (IsPartialIso.atom_iff h (mem_reach (p := []) hab (Nat.zero_le d)) s₁).mp h₁
  have hb' : b' = F'.atom s₂ :=
    (IsPartialIso.atom_iff h (mem_reach (p := []) hab' (Nat.zero_le d)) s₂).mp h₂
  rw [hb, hb']
  exact (F'.atom_append_atom _ _ _).mpr ht

lemma eq_append (h : F.Similar F' (d + 1) ρ) (hab : (a, b) ∈ ρ) (hab' : (a', b') ∈ ρ)
    (hxy : (x, y) ∈ F.Reach F' d ρ) (hx : x = a ++ a') : y = b ++ b' := by
  have hR : (x, y) ∈ F.Reach F' (d + 1) ρ := reach_mono (Nat.le_succ d) le_rfl hxy
  by_cases hat : F.IsAtom (a ++ a')
  · obtain ⟨s, hs⟩ := hat
    rw [h.append_eq_atom hab hab' hs]
    exact (IsPartialIso.atom_iff h hR s).mp (hx.trans hs)
  · have hy : ¬F'.IsAtom y := fun hy ↦ hat (hx ▸ (IsPartialIso.isAtom_iff h hR).mpr hy)
    have hl : F'.left y = b :=
      (IsPartialIso.eq_iff h (child_mem_reach hxy false)
        (mem_reach (p := []) hab (Nat.zero_le _))).mp (by rw [hx]; exact F.left_append hat)
    have hr : F'.right y = b' :=
      (IsPartialIso.eq_iff h (child_mem_reach hxy true)
        (mem_reach (p := []) hab' (Nat.zero_le _))).mp (by rw [hx]; exact F.right_append hat)
    rw [← F'.left_append_right hy, hl, hr]

lemma insert_append (h : F.Similar F' (d + 1) ρ) (hab : (a, b) ∈ ρ) (hab' : (a', b') ∈ ρ) :
    F.Similar F' d (insert (a ++ a', b ++ b') ρ) := by
  have hs : (b, a) ∈ Prod.swap '' ρ := ⟨(a, b), hab, rfl⟩
  have hs' : (b', a') ∈ Prod.swap '' ρ := ⟨(a', b'), hab', rfl⟩
  have hat (s : S) : a ++ a' = F.atom s ↔ b ++ b' = F'.atom s :=
    ⟨h.append_eq_atom hab hab', h.swap.append_eq_atom hs hs'⟩
  have h' : F.IsPartialIso F' (insert (a ++ a', b ++ b') (F.Reach F' d ρ)) :=
    IsPartialIso.insert (h.mono (Nat.le_succ d) le_rfl)
      (fun x y hxy ↦ ⟨h.eq_append hab hab' hxy, h.swap.eq_append hs hs' <| by
        rw [reach_swap]
        exact ⟨(x, y), hxy, rfl⟩⟩) hat
  apply h'.mono
  rw [reach_insert]
  rintro z (hz | ⟨p, hp, rfl⟩)
  · exact .inr hz
  · cases p with
    | nil => exact .inl rfl
    | cons i p =>
      by_cases ha : F.IsAtom (a ++ a')
      · rw [F.comp_of_isAtom ha, F'.comp_of_isAtom (ha.imp fun s ↦ (hat s).mp)]
        exact .inl rfl
      · have hb : ¬F'.IsAtom (b ++ b') := fun hb ↦ ha (hb.imp fun s ↦ (hat s).mpr)
        have hp' : p.length ≤ d := Nat.le_of_succ_le hp
        right
        cases i
        · simpa [F.left_append ha, F'.left_append hb] using mem_reach hab hp'
        · simpa [F.right_append ha, F'.right_append hb] using mem_reach hab' hp'

end Similar

variable (F F')

/--
Components up to a depth `g` depending only on `d` correspond: then every element on the left has a
partner on the right such that the components up to depth `d` still correspond.
-/
theorem exists_similar_insert (d : ℕ) : ∃ g, ∀ ρ : Set (M × M'), ρ.Finite → F.Similar F' g ρ →
    ∀ a, ∃ b, F.Similar F' d (insert (a, b) ρ) := by
  classical
  let P : List (List Bool) := (List.finite_length_le Bool d).toFinset.toList
  have hP (p : List Bool) (hp : p.length ≤ d) : p ∈ P := by simpa [P] using hp
  obtain ⟨K, hK⟩ : ∃ K, P.length = K := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = d + 2 ^ K + K + 1 := ⟨_, rfl⟩
  use g
  intro ρ hρ hE a
  let L : List M := P.map (F.comp · a)
  have hL (p : List Bool) (hp : p.length ≤ d) : F.comp p a ∈ L :=
    List.mem_map.mpr ⟨p, hP p hp, rfl⟩
  have hLK : L.length = K := by simp [L, hK]
  obtain ⟨θ, hdθ, hθ, hgap⟩ := exists_gap (fun j ↦ {x | ∃ y, (x, y) ∈ F.Reach F' j ρ})
    (fun i j hij x ⟨y, hy⟩ ↦ ⟨y, reach_mono hij le_rfl hy⟩) L d
  rw [hLK] at hθ
  have hmono {j : ℕ} (hj : j ≤ g) : F.Reach F' j ρ ⊆ F.Reach F' g ρ := reach_mono hj le_rfl
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, ∀ i, m₀ ≤ i → ∀ x, (x, F'.tower i) ∉ F.Reach F' g ρ := by
    have hfin : {i | ∃ x, (x, F'.tower i) ∈ F.Reach F' g ρ}.Finite :=
      (((finite_reach hρ).image Prod.snd).preimage F'.tower_injective.injOn).subset
        fun i ⟨x, hx⟩ ↦ ⟨(x, _), hx, rfl⟩
    obtain ⟨m, hm⟩ := hfin.bddAbove
    use m + 1
    intro i hi x hx
    have : i ≤ m := hm ⟨x, hx⟩
    omega
  obtain ⟨D, hD⟩ : ∃ D, D = K + 1 := ⟨_, rfl⟩
  have hDpos (i : ℕ) : D + 1 ≤ (D + 1) * (i + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos i)
  let m : M → ℕ := fun x ↦ m₀ + (D + 1) * (L.idxOf x + 1)
  let φ : M → M' := fun x ↦
    if h : ∃ y, (x, y) ∈ F.Reach F' θ ρ then h.choose
    else if h' : F.IsAtom x then F'.atom h'.choose else F'.tower (m x)
  let T : Set M := {x | (∃ p : List Bool, p.length < d ∧ x = F.comp p a) ∧ ¬F.IsAtom x ∧
    ¬∃ y, (x, y) ∈ F.Reach F' θ ρ}
  have hTL (x : M) (hx : x ∈ T) : x ∈ L := by
    obtain ⟨⟨p, hp, rfl⟩, -, -⟩ := hx
    exact hL p hp.le
  have hTc (x : M) (hx : x ∈ T) (i : Bool) : F.child i x ∈ L := by
    obtain ⟨⟨p, hp, rfl⟩, -, -⟩ := hx
    simpa using hL (p ++ [i]) (by simp; omega)
  obtain ⟨H, hH₀, hH₁, hHt⟩ := F.exists_copy (M' := M') (fun x (hx : x ∈ T) ↦ hx.2.1) L hTL φ
  rw [hLK] at hHt
  have hold {x : M} {y : M'} (hxy : (x, y) ∈ F.Reach F' θ ρ) : (x, H x) ∈ F.Reach F' θ ρ := by
    have h : ∃ y, (x, y) ∈ F.Reach F' θ ρ := ⟨y, hxy⟩
    rw [hH₀ x fun hx ↦ hx.2.2 h]
    simp only [φ, h, ↓reduceDIte]
    exact h.choose_spec
  have hatom {x : M} (s : S) (hx : ¬∃ y, (x, y) ∈ F.Reach F' θ ρ) (hs : x = F.atom s) :
      H x = F'.atom s := by
    have h' : F.IsAtom x := ⟨s, hs⟩
    rw [hH₀ x fun hxT ↦ hxT.2.1 h']
    simp only [φ, hx, h', ↓reduceDIte]
    rw [F.atom_injective (h'.choose_spec.symm.trans hs)]
  have hfresh {x : M} (hx : ¬∃ y, (x, y) ∈ F.Reach F' θ ρ) (hx' : ¬F.IsAtom x) (hxT : x ∉ T) :
      H x = F'.tower (m x) := by
    rw [hH₀ x hxT]
    simp only [φ, hx, hx', ↓reduceDIte]
  have hN (x : M) : ∀ s, H x = F'.atom s ↔ x = F.atom s := by
    apply F.heightLE_induction (P := fun _ x ↦ ∀ s, H x = F'.atom s ↔ x = F.atom s) _ _ K x
      (hHt x)
    · intro _ x hxT s
      by_cases ho : ∃ y, (x, y) ∈ F.Reach F' θ ρ
      · obtain ⟨y, hy⟩ := ho
        exact (IsPartialIso.atom_iff hE (hmono (by omega) (hold hy)) s).symm
      · by_cases ha : F.IsAtom x
        · obtain ⟨s', rfl⟩ := ha
          rw [hatom s' ho rfl, F.atom_injective.eq_iff, F'.atom_injective.eq_iff]
        · rw [hfresh ho ha hxT]
          exact ⟨fun h ↦ (F'.not_isAtom_tower _ ⟨s, h⟩).elim, fun h ↦ (ha ⟨s, h⟩).elim⟩
    · intro _ x hxT hl hr s
      rw [hH₁ x hxT]
      constructor
      · intro h
        obtain ⟨⟨s₁, h₁⟩, s₂, h₂⟩ := F'.exists_atom_of_append h
        have ht : tbl s₁ s₂ s := (F'.atom_append_atom _ _ _).mp (by rw [← h₁, ← h₂, h])
        rw [← F.left_append_right hxT.2.1, (hl s₁).mp h₁, (hr s₂).mp h₂]
        exact (F.atom_append_atom _ _ _).mpr ht
      · intro h
        exact (hxT.2.1 ⟨s, h⟩).elim
  have hnot (x : M) (hx : ¬F.IsAtom x) : ¬F'.IsAtom (H x) := fun ⟨s, hs⟩ ↦
    hx ⟨s, (hN x s).mp hs⟩
  have hnot' (x : M) (hx : x ∈ T) (s : S) : H (F.left x) ++ H (F.right x) ≠ F'.atom s := by
    have := hnot x hx.2.1
    rw [hH₁ x hx] at this
    exact not_exists.mp this s
  have hC (p : List Bool) (hp : p.length < d) (i : Bool) :
      F'.child i (H (F.comp p a)) = H (F.child i (F.comp p a)) := by
    obtain ⟨x, hx⟩ : ∃ x, x = F.comp p a := ⟨_, rfl⟩
    rw [← hx]
    have hcL : F.child i x ∈ L := by
      simpa [hx] using hL (p ++ [i]) (by simp; omega)
    by_cases ho : ∃ y, (x, y) ∈ F.Reach F' θ ρ
    · obtain ⟨y, hy⟩ := ho
      have h₁ := child_mem_reach (hold hy) i
      obtain ⟨y', hy'⟩ := hgap _ hcL ⟨_, h₁⟩
      exact (IsPartialIso.eq_iff hE (hmono (by omega) h₁) (hmono (by omega) (hold hy'))).mp rfl
    · by_cases ha : F.IsAtom x
      · obtain ⟨s, hs⟩ := ha
        rw [F.child_of_isAtom ⟨s, hs⟩, hatom s ho hs, F'.child_of_isAtom ⟨s, rfl⟩]
      · have hxT : x ∈ T := ⟨⟨p, hp, hx⟩, ha, ho⟩
        have := hnot x ha
        rw [hH₁ x hxT] at this ⊢
        cases i
        · exact F'.left_append this
        · exact F'.right_append this
  have h1 (p : List Bool) (hp : p.length ≤ d) : F'.comp p (H a) = H (F.comp p a) := by
    induction p using List.reverseRecOn with
    | nil => rfl
    | append_singleton p i ih =>
      have hp : p.length < d := by simp at hp; omega
      rw [comp_append, comp_append, ih hp.le]
      exact hC p hp i
  have hO (x : M) :
      ∀ j, j + K ≤ g → ∀ x₂ y₂, (x₂, y₂) ∈ F.Reach F' j ρ → H x = y₂ → x = x₂ := by
    apply F.heightLE_induction (P := fun n x ↦ ∀ j, j + n ≤ g → ∀ x₂ y₂,
      (x₂, y₂) ∈ F.Reach F' j ρ → H x = y₂ → x = x₂) _ _ K x (hHt x)
    · intro n x hxT j hj x₂ y₂ h₂ hxy
      have h₂' := hmono (by omega) h₂
      by_cases ho : ∃ y, (x, y) ∈ F.Reach F' θ ρ
      · obtain ⟨y, hy⟩ := ho
        exact (IsPartialIso.eq_iff hE (hmono (by omega) (hold hy)) h₂').mpr hxy
      · by_cases ha : F.IsAtom x
        · obtain ⟨s, rfl⟩ := ha
          exact ((IsPartialIso.atom_iff hE h₂' s).mpr (hxy.symm.trans (hatom s ho rfl))).symm
        · rw [hfresh ho ha hxT] at hxy
          exact (hm₀ (m x) (Nat.le_add_right _ _) x₂ (hxy ▸ h₂')).elim
    · intro n x hxT hl hr j hj x₂ y₂ h₂ hxy
      have h₂' := hmono (by omega) h₂
      rw [hH₁ x hxT] at hxy
      have hy₂ : ¬F'.IsAtom y₂ := fun ⟨s, hs⟩ ↦ hnot' x hxT s (hxy.trans hs)
      have hx₂ : ¬F.IsAtom x₂ := fun h ↦ hy₂ ((IsPartialIso.isAtom_iff hE h₂').mp h)
      have el : F.left x = F.left x₂ :=
        hl (j + 1) (by omega) _ _ (child_mem_reach h₂ false) <| by
          rw [child_false, ← hxy, F'.left_append (hxy ▸ hy₂)]
      have er : F.right x = F.right x₂ :=
        hr (j + 1) (by omega) _ _ (child_mem_reach h₂ true) <| by
          rw [child_true, ← hxy, F'.right_append (hxy ▸ hy₂)]
      rw [← F.left_append_right hxT.2.1, ← F.left_append_right hx₂, el, er]
  have hspace {i j t : ℕ} (ht : 1 ≤ t) (htD : t ≤ D) :
      (D + 1) * (j + 1) + t ≠ (D + 1) * (i + 1) := by
    intro h
    have : D + 1 ∣ t := (Nat.dvd_add_right (Nat.dvd_mul_right _ _)).mp (h ▸ Nat.dvd_mul_right _ _)
    have := Nat.le_of_dvd (by omega) this
    omega
  have hZ (x : M) : ∀ i t, 1 ≤ t → t + K ≤ D → H x ≠ F'.tower (m₀ + (D + 1) * (i + 1) - t) := by
    apply F.heightLE_induction (P := fun n x ↦ ∀ i t, 1 ≤ t → t + n ≤ D →
      H x ≠ F'.tower (m₀ + (D + 1) * (i + 1) - t)) _ _ K x (hHt x)
    · intro n x hxT i t ht htn hxe
      have hi := hDpos i
      by_cases ho : ∃ y, (x, y) ∈ F.Reach F' θ ρ
      · obtain ⟨y, hy⟩ := ho
        exact hm₀ (m₀ + (D + 1) * (i + 1) - t) (by omega) x (hxe ▸ hmono (by omega) (hold hy))
      · by_cases ha : F.IsAtom x
        · obtain ⟨s, rfl⟩ := ha
          exact F'.not_isAtom_tower _ ⟨s, hxe.symm.trans (hatom s ho rfl)⟩
        · rw [hfresh ho ha hxT] at hxe
          have := F'.tower_injective hxe
          apply hspace (i := i) (j := L.idxOf x) ht (by omega)
          simp only [m] at this
          omega
    · intro n x hxT hl hr i t ht htn hxe
      have hi := hDpos i
      obtain ⟨k, hk⟩ : ∃ k, m₀ + (D + 1) * (i + 1) - t = k + 1 :=
        ⟨m₀ + (D + 1) * (i + 1) - t - 1, by omega⟩
      rw [hH₁ x hxT, hk, tower_succ] at hxe
      apply hl i (t + 1) (by omega) (by omega)
      rw [show m₀ + (D + 1) * (i + 1) - (t + 1) = k by omega]
      exact (F'.append_injective (hnot' x hxT) hxe).1
  have hIo (x x' : M) (y : M') (hy : (x, y) ∈ F.Reach F' θ ρ) (h : H x = H x') : x' = x :=
    hO x' θ (by omega) x (H x) (hold hy) h.symm
  have hleaf (x x' : M) (ho : ¬∃ y, (x, y) ∈ F.Reach F' θ ρ) (ha : ¬F.IsAtom x) (hxT : x ∉ T)
      (hx'T : x' ∈ T) : H x ≠ H x' := by
    intro h
    have hi := hDpos (L.idxOf x)
    rw [hfresh ho ha hxT, hH₁ x' hx'T,
      show m x = m₀ + (D + 1) * (L.idxOf x + 1) - 1 + 1 by simp only [m]; omega, tower_succ] at h
    exact hZ (F.left x') (L.idxOf x) 1 le_rfl (by omega)
      (F'.append_injective (hnot' x' hx'T) h.symm).1
  have hI (x : M) : x ∈ L → ∀ x' ∈ L, H x = H x' → x = x' := by
    apply F.heightLE_induction (P := fun _ x ↦ x ∈ L → ∀ x' ∈ L, H x = H x' → x = x') _ _ K x
      (hHt x)
    · intro _ x hxT hxL x' hx'L h
      by_cases ho : ∃ y, (x, y) ∈ F.Reach F' θ ρ
      · obtain ⟨y, hy⟩ := ho
        exact (hIo x x' y hy h).symm
      by_cases ho' : ∃ y, (x', y) ∈ F.Reach F' θ ρ
      · obtain ⟨y, hy⟩ := ho'
        exact hIo x' x y hy h.symm
      by_cases ha : F.IsAtom x
      · obtain ⟨s, rfl⟩ := ha
        exact ((hN x' s).mp (h.symm.trans (hatom s ho rfl))).symm
      by_cases ha' : F.IsAtom x'
      · obtain ⟨s, rfl⟩ := ha'
        exact (hN x s).mp (h.trans (hatom s ho' rfl))
      by_cases hx'T : x' ∈ T
      · exact (hleaf x x' ho ha hxT hx'T h).elim
      rw [hfresh ho ha hxT, hfresh ho' ha' hx'T] at h
      have := F'.tower_injective h
      simp only [m] at this
      have := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos D) (Nat.add_left_cancel this)
      exact (List.idxOf_inj hxL).mp (by omega)
    · intro _ x hxT hl hr hxL x' hx'L h
      by_cases ho' : ∃ y, (x', y) ∈ F.Reach F' θ ρ
      · obtain ⟨y, hy⟩ := ho'
        exact hIo x' x y hy h.symm
      by_cases ha' : F.IsAtom x'
      · obtain ⟨s, rfl⟩ := ha'
        exact (hxT.2.1 ⟨s, (hN x s).mp (h.trans (hatom s ho' rfl))⟩).elim
      by_cases hx'T : x' ∈ T
      · rw [hH₁ x hxT, hH₁ x' hx'T] at h
        obtain ⟨e₁, e₂⟩ := F'.append_injective (hnot' x hxT) h
        rw [← F.left_append_right hxT.2.1, ← F.left_append_right hx'T.2.1,
          hl (hTc x hxT false) _ (hTc x' hx'T false) e₁,
          hr (hTc x hxT true) _ (hTc x' hx'T true) e₂]
        rfl
      · exact (hleaf x' x ho' ha' hx'T hxT h.symm).elim
  use H a
  have hsub : F.Reach F' d (insert (a, H a) ρ) ⊆
      F.Reach F' d ρ ∪ {z | ∃ x ∈ L, z = (x, H x)} := by
    rw [reach_insert]
    rintro z (hz | ⟨p, hp, rfl⟩)
    · exact .inl hz
    · exact .inr ⟨_, hL p hp, by rw [h1 p hp]⟩
  have hdg {z : M × M'} (hz : z ∈ F.Reach F' d ρ) : z ∈ F.Reach F' g ρ := hmono (by omega) hz
  have hOld {x₂ x : M} {y₂ : M'} (h₂ : (x₂, y₂) ∈ F.Reach F' d ρ) : x₂ = x ↔ y₂ = H x := by
    constructor
    · rintro rfl
      have h := hmono (by omega) (hold (reach_mono hdθ le_rfl h₂))
      exact (IsPartialIso.eq_iff hE (hdg h₂) h).mp rfl
    · intro h
      exact (hO x d (by omega) x₂ y₂ h₂ h.symm).symm
  apply IsPartialIso.mono _ hsub
  constructor
  · rintro x x' y y' (h | ⟨u, hu, e⟩) (h' | ⟨u', hu', e'⟩)
    · exact IsPartialIso.eq_iff hE (hdg h) (hdg h')
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
      exact hOld h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      rw [eq_comm, hOld h', eq_comm]
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
      exact ⟨fun h ↦ h ▸ rfl, hI x hu x' hu'⟩
  · rintro x y (h | ⟨u, hu, e⟩) s
    · exact IsPartialIso.atom_iff hE (hdg h) s
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      exact (hN x s).symm

/-- The same as `exists_similar_insert`, for an element on the right. -/
lemma exists_similar_insert' (d : ℕ) : ∃ g, ∀ ρ : Set (M × M'), ρ.Finite → F.Similar F' g ρ →
    ∀ b, ∃ a, F.Similar F' d (insert (a, b) ρ) := by
  obtain ⟨g, hg⟩ := exists_similar_insert F' F d
  use g
  intro ρ hρ h b
  obtain ⟨a, ha⟩ := hg _ (hρ.image _) h.swap b
  use a
  simpa [Set.image_insert_eq, Set.image_image] using ha.swap

end

end AtomicPairing
