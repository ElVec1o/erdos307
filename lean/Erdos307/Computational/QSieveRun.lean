import Erdos307.Computational.QSieveBase
import Erdos307.KillData

/-! Timing and cross-check driver (instrument, not part of any proof): `qrun a n` runs `sieveBase` on the survivor pools
`a .. a+n-1` and prints the result and the time per base. -/

open Erdos307

def main (args : List String) : IO Unit := do
  let a := args[0]!.toNat!
  let n := args[1]!.toNat!
  let pools := (survivorPools.drop a).take n
  let mut ok := 0
  let mut t0 ← IO.monoMsNow
  for V in pools do
    let r := sieveBase (forced39 ++ V)
    let t1 ← IO.monoMsNow
    IO.println s!"pool {a + ok} result {r} ms {t1 - t0}"
    t0 := t1
    ok := ok + 1
