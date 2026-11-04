module

public import InducedPaths.C6Named
public meta import InducedPaths.C6Named
public meta import InducedPaths.Graphs

open scoped SimpleGraph
open SimpleGraph

@[expose] public section
namespace InducedPaths

def shapeAddress (k h : ℕ) : HexShapeV k h → Fin (6+k+h)
  | .inl i => ⟨i.val, by omega⟩
  | .inr (.inl j) => ⟨6+j.val, by omega⟩
  | .inr (.inr j) => ⟨6+k+j.val, by omega⟩

def h8Address : Fin 8 → H8V :=
  ![.cycle 0, .cycle 1, .cycle 2, .cycle 3, .cycle 4, .cycle 5, .extra 0, .extra 1]

def h8Table (f : Fin 2 → Fin 3) : Fin 8 → Fin 8 :=
  if f 0 = 0 then
    if f 1 = 1 then ![0,1,2,3,4,5,6,7] else ![0,6,3,4,7,1,5,2]
  else if f 0 = 1 then
    if f 1 = 0 then ![0,1,2,3,4,5,7,6] else ![5,0,1,2,3,4,6,7]
  else
    if f 1 = 0 then ![0,6,3,4,7,1,2,5] else ![5,0,1,2,3,4,7,6]

def h8ShapeMap (f : Fin 2 → Fin 3) (v : HexShapeV 2 0) : H8V :=
  h8Address (h8Table f (shapeAddress 2 0 v))

theorem h8ShapeMap_certificate : ∀ f : Fin 2 → Fin 3,
    Function.Injective f → Function.Bijective (h8ShapeMap f) ∧
      ∀ u v, h8Graph.Adj (h8ShapeMap f u) (h8ShapeMap f v) ↔
        (hexShape 2 0 f).Adj u v := by native_decide

noncomputable def hexShapeTwoZeroIsoH8 (f : Fin 2 → Fin 3)
    (hf : Function.Injective f) : hexShape 2 0 f ≃g h8Graph :=
  { Equiv.ofBijective (h8ShapeMap f) (h8ShapeMap_certificate f hf).1 with
    map_rel_iff' := fun {u v} => (h8ShapeMap_certificate f hf).2 u v }

def minusAddress : Fin 9 → {s : PetersenVertex // s ≠ petersenHub} :=
  ![⟨⟨{0,2}, by decide⟩, by decide⟩, ⟨⟨{0,3}, by decide⟩, by decide⟩,
    ⟨⟨{0,4}, by decide⟩, by decide⟩, ⟨⟨{1,2}, by decide⟩, by decide⟩,
    ⟨⟨{1,3}, by decide⟩, by decide⟩, ⟨⟨{1,4}, by decide⟩, by decide⟩,
    ⟨⟨{2,3}, by decide⟩, by decide⟩, ⟨⟨{2,4}, by decide⟩, by decide⟩,
    ⟨⟨{3,4}, by decide⟩, by decide⟩]

def minusTwoTable (f : Fin 2 → Fin 3) : Fin 9 → Fin 9 :=
  if f 0 = 0 then
    if f 1 = 1 then ![0,4,7,1,3,8,5,2,6] else ![0,8,3,1,7,4,5,2,6]
  else if f 0 = 1 then
    if f 1 = 0 then ![0,4,7,1,3,8,2,5,6] else ![8,0,4,7,1,3,5,2,6]
  else
    if f 1 = 0 then ![0,8,3,1,7,4,2,5,6] else ![8,0,4,7,1,3,2,5,6]

def minusTwoMap (f : Fin 2 → Fin 3) (v : HexShapeV 2 1) :
    {s : PetersenVertex // s ≠ petersenHub} :=
  minusAddress (minusTwoTable f (shapeAddress 2 1 v))

theorem minusTwoMap_certificate : ∀ f : Fin 2 → Fin 3,
    Function.Injective f → Function.Bijective (minusTwoMap f) ∧
      ∀ u v, petersenMinus.Adj (minusTwoMap f u) (minusTwoMap f v) ↔
        (hexShape 2 1 f).Adj u v := by native_decide

noncomputable def hexShapeTwoOneIsoPetersenMinus (f : Fin 2 → Fin 3)
    (hf : Function.Injective f) : hexShape 2 1 f ≃g petersenMinus :=
  { Equiv.ofBijective (minusTwoMap f) (minusTwoMap_certificate f hf).1 with
    map_rel_iff' := fun {u v} => (minusTwoMap_certificate f hf).2 u v }

def minusThreeMap (f : Fin 3 → Fin 3) : HexShapeV 3 0 →
    {s : PetersenVertex // s ≠ petersenHub}
  | .inl i => minusAddress ((![0,4,2,3,1,5] : Fin 6 → Fin 9) i)
  | .inr (.inl j) => minusAddress ((![8,7,6] : Fin 3 → Fin 9) (f j))
  | .inr (.inr j) => Fin.elim0 j

theorem minusThreeMap_certificate : ∀ f : Fin 3 → Fin 3,
    Function.Injective f → Function.Bijective (minusThreeMap f) ∧
      ∀ u v, petersenMinus.Adj (minusThreeMap f u) (minusThreeMap f v) ↔
        (hexShape 3 0 f).Adj u v := by native_decide

noncomputable def hexShapeThreeZeroIsoPetersenMinus (f : Fin 3 → Fin 3)
    (hf : Function.Injective f) : hexShape 3 0 f ≃g petersenMinus :=
  { Equiv.ofBijective (minusThreeMap f) (minusThreeMap_certificate f hf).1 with
    map_rel_iff' := fun {u v} => (minusThreeMap_certificate f hf).2 u v }

end InducedPaths
