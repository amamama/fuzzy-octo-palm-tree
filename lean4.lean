
def main : IO Unit :=
  IO.println "Hello, world!"

theorem test1 {α} (a b : α) (as bs : List α) (h : a::as = b::bs) : a = b :=
by {
  injection h;
  assumption;
}