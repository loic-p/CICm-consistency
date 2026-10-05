From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Layer1.Per Layer1.Def Ranks.Pred.

(* Brouwer trees whose sups are indexed by component witnesses. *)
Inductive Ord : Type :=
| ozero : Ord
| osucc : Ord -> Ord
| osup : forall T : etm, (Pred T -> Ord) -> Ord.

(* Structural simulation: the only order on trees the code hierarchy needs.
   osim a b says every branch of a is matched by a branch of b, through an
   explicit reindexing of the sup indices.  It is Type-valued and computed by
   recursion, so that codes can be transported along it without inverting a
   dependent inductive. *)
Fixpoint osim (a b : Ord) : Type :=
  match a, b with
  | ozero, ozero => unit
  | osucc a, osucc b => osim a b
  | osup T f, osup T' g => { phi : Pred T -> Pred T' & forall p, osim (f p) (g (phi p)) }
  | _, _ => Empty_set
  end.

Fixpoint osim_refl (a : Ord) : osim a a :=
  match a with
  | ozero => tt
  | osucc a => osim_refl a
  | osup T f => existT _ (fun p => p) (fun p => osim_refl (f p))
  end.

Fixpoint osim_trans (a : Ord) : forall b c, osim a b -> osim b c -> osim a c :=
  match a with
  | ozero => fun b c => match b, c with
      | ozero, ozero => fun _ _ => tt
      | ozero, _ => fun _ e => match e with end
      | _, _ => fun e _ => match e with end
      end
  | osucc a => fun b c => match b, c with
      | osucc b, osucc c => fun s t => osim_trans a b c s t
      | osucc b, _ => fun _ e => match e with end
      | _, _ => fun e _ => match e with end
      end
  | osup T f => fun b c => match b, c with
      | osup T' g, osup T'' h => fun s t =>
          existT _ (fun p => projT1 t (projT1 s p))
            (fun p => osim_trans _ _ _ (projT2 s p) (projT2 t (projT1 s p)))
      | osup T' g, _ => fun _ e => match e with end
      | _, _ => fun e _ => match e with end
      end
  end.

(* Reindexing a sup along a bijection of witnesses gives a simulation in both
   directions; this is how rank irrelevance and reduction-invariance of the
   rank reach the code hierarchy. *)
Definition osim_sup_reindex {T T'} (f : Pred T -> Ord) (g : Pred T' -> Ord)
  (phi : Pred T -> Pred T') (H : forall p, osim (f p) (g (phi p))) :
  osim (osup T f) (osup T' g) := existT _ phi H.
