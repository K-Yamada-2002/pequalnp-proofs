import Std

namespace BowtieFinite

-- Bits 0 to 29 are the negative endpoints and bits 30 to 59 their positive partners.
-- Bits 60 to 64 record the five singleton assignments.
abbrev W := BitVec 65

def start : List W := [0x107fe0ffc2108421, 0x20001f07d4a5294a, 0x40001ff8294a5294, 0x8f83e0000c6318c6, 0x10ffc0000318c6318]

def target : W := 0xfffffffc0000000

def separated (w : W) : BitVec 30 := ((w >>> 30) &&& ~~~w).setWidth 30

def covered (ws : List W) : BitVec 30 := ws.foldr (fun w m => separated w ||| m) 0

def wide (w : W) : Bool :=
  let singles := w >>> 60
  singles &&& (singles - 1) != 0

def pick {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: t => (a,t) :: (pick t).map (fun (b,r) => (b,a::r))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: t => ((pick t).map fun (b,r) => (a,b,r)) ++
      ((pairs t).map fun (b,c,r) => (b,c,a::r))

def explore (next : List W → Bool) (remaining : Nat) (a b z : W) (rest : List W) : Bool :=
  if z == a || z == b || rest.contains z then false else
  let cover := covered rest ||| separated z
  let size := rest.length
  (size ≤ remaining && cover == -1 && next (z :: rest)) ||
    (size + 1 ≤ remaining && ((cover ||| separated a == -1 && next (z :: a :: rest)) ||
      (cover ||| separated b == -1 && next (z :: b :: rest)))) ||
    (size + 2 ≤ remaining && cover ||| separated a ||| separated b == -1 &&
      next (z :: a :: b :: rest))

def stepPair (k : Nat) (one two : List W → Bool) (p : W × W × List W) : Bool :=
  let (a,b,r) := p
  let disj := a ||| b
  explore one k a b (a &&& b) r ||
    (if wide disj then explore one k a b disj r else
       k != 0 && explore two (k-1) a b disj r)

def run : Nat → List W → Bool
  | 0, ws => ws.contains target
  | 1, ws => ws.contains target || (pairs ws).any (stepPair 0 (run 0) (fun _ => false))
  | k+2, ws => ws.contains target || (pairs ws).any (stepPair (k+1) (run (k+1)) (run k))

#eval (run 9 start, run 10 start)
end BowtieFinite
