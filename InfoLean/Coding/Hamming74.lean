import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation

namespace InfoLean.Coding

open Matrix

/-- Generator matrix for the (7,4) Hamming code. -/
def hammingG : Matrix (Fin 4) (Fin 7) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 1, 0],
    ![0, 1, 0, 0, 1, 0, 1],
    ![0, 0, 1, 0, 0, 1, 1],
    ![0, 0, 0, 1, 1, 1, 1]]

/-- Parity-check matrix for the (7,4) Hamming code. -/
def hammingH : Matrix (Fin 3) (Fin 7) (ZMod 2) :=
  ![![1, 1, 0, 1, 1, 0, 0],
    ![1, 0, 1, 1, 0, 1, 0],
    ![0, 1, 1, 1, 0, 0, 1]]

/-- Encode a 4-bit message into a 7-bit codeword. -/
def encode (s : Fin 4 → ZMod 2) : Fin 7 → ZMod 2 :=
  hammingG.transpose.mulVec s

/-- Compute the syndrome of a received word. -/
def syndrome (r : Fin 7 → ZMod 2) : Fin 3 → ZMod 2 :=
  hammingH.mulVec r

/-- Standard basis vector in `Fin 7`. -/
def basis7 (i : Fin 7) : Fin 7 → ZMod 2 :=
  fun j => if j = i then 1 else 0

def s000 : Fin 3 → ZMod 2 := ![0, 0, 0]
def s110 : Fin 3 → ZMod 2 := ![1, 1, 0]
def s101 : Fin 3 → ZMod 2 := ![1, 0, 1]
def s011 : Fin 3 → ZMod 2 := ![0, 1, 1]
def s111 : Fin 3 → ZMod 2 := ![1, 1, 1]
def s100 : Fin 3 → ZMod 2 := ![1, 0, 0]
def s010 : Fin 3 → ZMod 2 := ![0, 1, 0]
def s001 : Fin 3 → ZMod 2 := ![0, 0, 1]

/-- Lookup table from syndromes to the error position. -/
def syndromeToIndex (s : Fin 3 → ZMod 2) : Option (Fin 7) := by
  classical
  exact if s = s000 then none
    else if s = s110 then some 0
    else if s = s101 then some 1
    else if s = s011 then some 2
    else if s = s111 then some 3
    else if s = s100 then some 4
    else if s = s010 then some 5
    else if s = s001 then some 6
    else none

/-- Error vector associated to a syndrome. -/
def errorVector (s : Fin 3 → ZMod 2) : Fin 7 → ZMod 2 :=
  match syndromeToIndex s with
  | none => 0
  | some i => basis7 i

/-- Decode to a codeword by correcting the indicated single-bit error. -/
def decodeCodeword (r : Fin 7 → ZMod 2) : Fin 7 → ZMod 2 :=
  r + errorVector (syndrome r)

/-- Extract the message bits from a codeword. -/
def messageOfCodeword (c : Fin 7 → ZMod 2) : Fin 4 → ZMod 2 :=
  ![c 0, c 1, c 2, c 3]

/-- Decode a received word to a 4-bit message. -/
def decodeMessage (r : Fin 7 → ZMod 2) : Fin 4 → ZMod 2 :=
  messageOfCodeword (decodeCodeword r)

end InfoLean.Coding
