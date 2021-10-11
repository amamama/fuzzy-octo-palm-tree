
def main : IO Unit :=
  IO.println "Hello, world!"

theorem test1 {α} (a b : α) (as bs : List α) (h : a::as = b::bs) : a = b :=
by {
  injection h;
  assumption;
}
inductive Mem : α → List α → Prop where
 | head (a : α) (as : List α)   : Mem a (a::as)
 | tail (a b : α) (bs : List α) : Mem a bs → Mem a (b::bs)
infix:50 "∈" => Mem
theorem mem_split {a : α} {as : List α} (h : a ∈ as) : ∃ s t, as = s ++ a :: t := by
  match a, as, h with
  | _, _, Mem.head a bs     => exists []; exists bs; rfl
  | _, _, Mem.tail a b bs h =>
    match bs, mem_split h with
    | _, ⟨s, ⟨t, rfl⟩⟩ =>
      exists b::s; exists t;
      rw [List.cons_append]