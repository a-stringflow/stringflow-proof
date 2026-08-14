import CycleBridge

namespace StringFlow

namespace CycleBridge

/-- Decomposition of a closed QB-8 word into the blocks used by the
PMI summation.  A block consists of a reset step into `headDepth r`,
the following rise suffix, and the C3 separator weight to the next
head. -/
structure CycleBlockDecomposition (m S P : Nat) (w : List Nat) where
  blockCount : Nat
  headDepth : Nat → Nat
  resetWeight : Nat → Nat
  suffixWord : Nat → List Nat
  c3Weight : Nat → Nat
  hhead0 : headDepth 0 = 0
  hhead_pos : ∀ r, r < blockCount → 1 ≤ headDepth r
  hhead_lt : ∀ r, r < blockCount → headDepth r < P
  hreset_eq : ∀ r, r < blockCount →
    resetWeight r = w.getI (headDepth r - 1)
  hreset_ge3 : ∀ r, r < blockCount → 3 ≤ resetWeight r
  hsuffix_one_two : ∀ r, r < blockCount →
     ∀ t ∈ suffixWord r, t = 1 ∨ t = 2
  hsuffix_exact : ∀ r, r < blockCount →
    ∀ k, k < (suffixWord r).length →
      twoValuation
        (5 * riseRun (StringFlow.Word.wordOrbit (w.take (headDepth r)) m)
          ((suffixWord r).take k) + 1)
      = (suffixWord r).getI k
  hc3_weight : ∀ r, r < blockCount → 3 ≤ c3Weight r
  hnext : ∀ r, r < blockCount →
    (if r + 1 < blockCount then headDepth (r + 1) else P) =
      headDepth r + resetWeight r + (suffixWord r).length + c3Weight r
  hweight : S =
    ((List.range blockCount).map
      (fun r => resetWeight r + StringFlow.wordWeight (suffixWord r) +
        c3Weight r)).sum

/-- Rank of the head of a block. -/
def cycleBlockHeadRank {m S P : Nat} {w : List Nat}
    (d : CycleBlockDecomposition m S P w) (r : Nat) : Nat :=
  twoValuation
    (StringFlow.Word.wordOrbit (w.take (d.headDepth r)) m + 1)

/-- Total positive charge along the suffix of a block. -/
def cycleBlockCharge {m S P : Nat} {w : List Nat}
    (d : CycleBlockDecomposition m S P w) (r : Nat) : Nat :=
  riseChargeSum
    (StringFlow.Word.wordOrbit (w.take (d.headDepth r)) m)
    (d.suffixWord r)

/-- The local rise-block balance specialized to one block of a
cycle decomposition. -/
theorem cycle_block_balance
    {m S P : Nat} {w : List Nat}
    (d : CycleBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    2 * riseCountTwo (d.suffixWord r) ≤
      cycleBlockHeadRank d r + cycleBlockCharge d r := by
  exact rise_block_balance
    (StringFlow.Word.wordOrbit (w.take (d.headDepth r)) m)
    (d.suffixWord r)
    (d.hsuffix_one_two r hr)
    (d.hsuffix_exact r hr)

/-- If a block avoids the decisive window, then its `t=2` count
satisfies the local capacity bound. -/
theorem cycle_block_H2_bound_of_avoid
    {m S P : Nat} {w : List Nat}
    (d : CycleBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (havoid : cycleBlockHeadRank d r + cycleBlockCharge d r ≤
      2 * (d.headDepth r - d.resetWeight r) + 12) :
    riseCountTwo (d.suffixWord r) ≤
      d.headDepth r - d.resetWeight r + 6 := by
  let u := cycleBlockHeadRank d r
  let F := cycleBlockCharge d r
  let H2 := riseCountTwo (d.suffixWord r)
  have hbal : 2 * H2 ≤ u + F := by
    dsimp [u, F, H2]
    exact cycle_block_balance d r hr
  have hwindow : u ≤ 2 * (d.headDepth r - d.resetWeight r) + 12 := by
    dsimp [u, F] at havoid ⊢
    omega
  have hcharge : F ≤ 2 * (d.headDepth r - d.resetWeight r) + 12 - u := by
    dsimp [u, F] at havoid ⊢
    omega
  exact block_capacity_of_charge_bound
    (d.headDepth r) (d.resetWeight r) u F H2 hbal hwindow hcharge

/-- The block satisfies the decisive non-failure budget. -/
def cycleBlockAvoidsWindow {m S P : Nat} {w : List Nat}
    (d : CycleBlockDecomposition m S P w) (r : Nat) : Prop :=
  cycleBlockHeadRank d r + cycleBlockCharge d r ≤
    2 * (d.headDepth r - d.resetWeight r) + 12

/-- Every block avoids the window.  This is the hypothesis used in the
PMI contradiction. -/
def cycleAllBlocksAvoidWindow {m S P : Nat} {w : List Nat}
    (d : CycleBlockDecomposition m S P w) : Prop :=
  ∀ r, r < d.blockCount → cycleBlockAvoidsWindow d r

/-- The remaining PMI contradiction target. -/
def pmicontradictionOfAllBlocksAvoid (m S P : Nat) (w : List Nat) : Prop :=
  ∀ d : CycleBlockDecomposition m S P w,
    ¬ cycleAllBlocksAvoidWindow d

/-- The empty decomposition shows that the unconstrained target is false:
it must also require a nonempty block decomposition, and ultimately a real
`CycleQb8Input`. -/
def emptyCycleBlockDecomposition : CycleBlockDecomposition 0 0 0 [] where
  blockCount := 0
  headDepth := fun _ => 0
  resetWeight := fun _ => 0
  suffixWord := fun _ => []
  c3Weight := fun _ => 0
  hhead0 := rfl
  hhead_pos := by
    intro r hr
    omega
  hhead_lt := by
    intro r hr
    omega
  hreset_eq := by
    intro r hr
    omega
  hreset_ge3 := by
    intro r hr
    omega
  hsuffix_one_two := by
    intro r hr t ht
    omega
  hsuffix_exact := by
    intro r hr k hk
    omega
  hc3_weight := by
    intro r hr
    omega
  hnext := by
    intro r hr
    omega
  hweight := by
    simp

/-- With zero blocks, the all-blocks-avoid condition is vacuously true. -/
theorem emptyCycleBlockDecomposition_allAvoid :
    cycleAllBlocksAvoidWindow emptyCycleBlockDecomposition := by
  intro r hr
  simp [emptyCycleBlockDecomposition] at hr

/-- The unconstrained PMI contradiction is false. -/
theorem pmicontradictionOfAllBlocksAvoid_false :
    ¬ pmicontradictionOfAllBlocksAvoid 0 0 0 [] := by
  intro h
  exact h emptyCycleBlockDecomposition emptyCycleBlockDecomposition_allAvoid

/-- A `CycleQb8Input` is anchored at a rise step. Consequently, a nonempty
linear decomposition beginning at word index zero cannot have a C3 reset
step at that position.  The block decomposition must instead use a cyclic
C3-to-rise boundary, which is why the real PMI contradiction cannot be
stated on the current linear `CycleBlockDecomposition`. -/
theorem cycleQb8Input_no_linear_block_decomposition
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (d : CycleBlockDecomposition m S P w)
    (hblock : 1 ≤ d.blockCount) : False := by
  have hreset0 := d.hreset_eq 0 hblock
  have hge3 := d.hreset_ge3 0 hblock
  rw [d.hhead0] at hreset0
  rw [hreset0] at hge3
  rcases h.hrise_start with h1 | h2
  · rw [h1] at hge3
    omega
  · rw [h2] at hge3
    omega

end CycleBridge

end StringFlow
