module

/-!
`Stack α` — a thin list-backed stack with the `popₙ` helpers used by EVM
opcodes. Faithful to the reference's `EvmYul.Data.Stack`.

We keep `push` cons-to-front, so `stack[0]` is the top of the stack.
The depth limit (1024) is enforced by the semantics, not the data type.
-/

@[expose] public section

namespace EvmSemantics

/-- An EVM-style operand stack, modelled as a list with `push` cons-to-front. -/
abbrev Stack (α : Type) := List α

namespace Stack

variable {α : Type}

/-- The empty stack. -/
def new : Stack α := []
/-- True iff the stack has no elements. -/
def isEmpty (s : Stack α) : Bool := List.isEmpty s
/-- Number of elements on the stack. -/
def size (s : Stack α) : Nat := List.length s
/-- Push `v` onto the top of `s`. -/
def push (s : Stack α) (v : α) : Stack α := v :: s

/-- Pop the top of the stack; `none` if empty. -/
def pop : Stack α → Option (Stack α × α)
  | hd :: tl => some (tl, hd)
  | []       => none

/-- Pop the top two elements; `none` if fewer than 2. -/
def pop2 : Stack α → Option (Stack α × α × α)
  | a :: b :: tl => some (tl, a, b)
  | _            => none

/-- Pop the top three elements. -/
def pop3 : Stack α → Option (Stack α × α × α × α)
  | a :: b :: c :: tl => some (tl, a, b, c)
  | _                 => none

/-- Pop the top four elements. -/
def pop4 : Stack α → Option (Stack α × α × α × α × α)
  | a :: b :: c :: d :: tl => some (tl, a, b, c, d)
  | _                      => none

/-- Pop the top five elements. -/
def pop5 : Stack α → Option (Stack α × α × α × α × α × α)
  | a :: b :: c :: d :: e :: tl => some (tl, a, b, c, d, e)
  | _                           => none

/-- Pop the top six elements. -/
def pop6 : Stack α → Option (Stack α × α × α × α × α × α × α)
  | a :: b :: c :: d :: e :: f :: tl => some (tl, a, b, c, d, e, f)
  | _                                => none

/-- Pop the top seven elements (the largest `popₙ` EVM needs — for `CALL`). -/
def pop7 : Stack α → Option (Stack α × α × α × α × α × α × α × α)
  | a :: b :: c :: d :: e :: f :: g :: tl => some (tl, a, b, c, d, e, f, g)
  | _                                     => none

/-- Duplicate the `n`-th element (1-indexed) onto the top. -/
def dup (n : Nat) (s : Stack α) : Option (Stack α) :=
  match s[n - 1]? with
  | some v => some (v :: s)
  | none   => none

/-- Swap the top with the `(n+1)`-th element. -/
def swap (n : Nat) (s : Stack α) : Option (Stack α) :=
  match s with
  | top :: rest =>
    if h : n - 1 < rest.length then
      let mid := rest[n - 1]
      let pre := rest.take (n - 1)
      let suf := rest.drop n
      some (mid :: pre ++ top :: suf)
    else
      none
  | [] => none

/-- Swap the elements at indices `i` and `j` (zero-indexed from the top).
    Returns `none` if either index is out of range. -/
def exchange (s : Stack α) (i j : Nat) : Option (Stack α) := do
  let xi ← s[i]?
  let xj ← s[j]?
  return (s.set i xj).set j xi

instance : Inhabited (Stack α) := ⟨new⟩
instance : EmptyCollection (Stack α) := ⟨new⟩

end Stack

end EvmSemantics
