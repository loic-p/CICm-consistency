From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str
  Codes.Sound Codes.Expand Codes.Mor Codes.Levels.
From Stdlib Require Import Arith Lia.

(* THE LEVEL LIFT.

   Codes/Mor.v did one node; this file does the recursion over the Brouwer
   tree and then the instance level k into level S k.

   The shape is dictated by one fact (DESIGN.md sec. 12): v2's equality is
   heterogeneous, so the diagonal comparison `xcmp alpha alpha` is not
   structural -- at a successor it compares a node's code with the codes below
   it through `xcmp (osucc beta) beta`.  The element maps' obligations
   therefore need the PAIR statement, and the pair statement mentions the
   morphism at two ordinals, so the Type-level data and the Prop-level pair
   facts depend on each other.

   The way out: the data's shape is explicit -- `SD alpha` is a nested tuple
   with one node morphism per node in the cone of alpha, so that the
   stage-level dispatch is definitional -- and the invariant is the single
   equation "each node morphism IS the standard construction from its
   restriction" (`NodeStd`).  From that, and nothing else, the pair statement
   follows by one nested induction (`pres_pair`), and the data is then a
   plain recursion. *)

Section Hierarchy.
Context (U1 U2 : nat -> etm -> Type)
        (E1 : forall m u, U1 m u -> forall m' u', U1 m' u' -> Prop)
        (E2 : forall m u, U2 m u -> forall m' u', U2 m' u' -> Prop)
        (OK1 OK2 : nat -> Prop).
Context (um : UMor U1 U2 E1 E2 OK1 OK2).
Context (UErefl1 : forall m u x, E1 m u x m u x)
        (UEsym1 : forall m u x m' u' x', E1 m u x m' u' x' -> E1 m' u' x' m u x)
        (UEtrans1 : forall m u x m' u' x' m'' u'' x'',
            E1 m u x m' u' x' -> E1 m' u' x' m'' u'' x'' -> E1 m u x m'' u'' x'')
        (UErefl2 : forall m u x, E2 m u x m u x)
        (UEsym2 : forall m u x m' u' x', E2 m u x m' u' x' -> E2 m' u' x' m u x)
        (UEtrans2 : forall m u x m' u' x' m'' u'' x'',
            E2 m u x m' u' x' -> E2 m' u' x' m'' u'' x'' -> E2 m u x m'' u'' x'').

(* ---- the two hierarchies ---- *)
Local Notation stage1_ := (stage U1 OK1).
Local Notation stage2_ := (stage U2 OK2).
Local Notation Ust1_ := (Ust U1 OK1).
Local Notation Ust2_ := (Ust U2 OK2).
Local Notation Sub1_ := (Sub U1 OK1).
Local Notation Sub2_ := (Sub U2 OK2).
Local Notation xc1_ := (xcmp U1 E1 OK1).
Local Notation xc2_ := (xcmp U2 E2 OK2).
Local Notation xcU1_ := (xcmpU U1 E1 OK1).
Local Notation xcU2_ := (xcmpU U2 E2 OK2).
Local Notation wfs1_ := (wfsub U1 E1 OK1).
Local Notation wfs2_ := (wfsub U2 E2 OK2).
Local Notation wfc1_ := (wfc U1 E1 OK1).
Local Notation wfc2_ := (wfc U2 E2 OK2).

(* the structure of each hierarchy, from Codes/Sym.v and Codes/Str.v, in the
   argument order Codes/Mor.v asks for *)
Definition sy1 {a a'} := xsym U1 E1 OK1 UEsym1 (alpha := a) (alpha' := a').
Definition sy2 {a a'} := xsym U2 E2 OK2 UEsym2 (alpha := a) (alpha' := a').

Definition tr1 (a b c : Ord) (s : Sub1_ a) (s' : Sub1_ b) (s'' : Sub1_ c)
  : forall u x u' x' u'' x'', wfs1_ a s -> wfs1_ b s' -> wfs1_ c s'' ->
      cU (xc1_ a b) s s' -> cEl (xc1_ a b) s u x s' u' x' ->
      cEl (xc1_ b c) s' u' x' s'' u'' x'' -> cEl (xc1_ a c) s u x s'' u'' x'' :=
  proj1 (proj2 (pk_tr U1 E1 OK1 a (big U1 E1 OK1 UErefl1 UEsym1 UEtrans1 a) b c s s' s'')).

Definition tr2 (a b c : Ord) (s : Sub2_ a) (s' : Sub2_ b) (s'' : Sub2_ c)
  : forall u x u' x' u'' x'', wfs2_ a s -> wfs2_ b s' -> wfs2_ c s'' ->
      cU (xc2_ a b) s s' -> cEl (xc2_ a b) s u x s' u' x' ->
      cEl (xc2_ b c) s' u' x' s'' u'' x'' -> cEl (xc2_ a c) s u x s'' u'' x'' :=
  proj1 (proj2 (pk_tr U2 E2 OK2 a (big U2 E2 OK2 UErefl2 UEsym2 UEtrans2 a) b c s s' s'')).

(* the shapes Codes/Mor.v's sections take: the wf arguments come first *)
Definition ssym1_ (a : Ord) : forall s u x s' u' x',
    cEl (xc1_ a a) s u x s' u' x' -> cEl (xc1_ a a) s' u' x' s u x := sy1.
Definition ssym2_ (a : Ord) : forall s u x s' u' x',
    cEl (xc2_ a a) s u x s' u' x' -> cEl (xc2_ a a) s' u' x' s u x := sy2.

Definition strE1_ (a : Ord) : forall s s' s'' u x u' x' u'' x'',
    wfs1_ a s -> wfs1_ a s' -> wfs1_ a s'' -> cU (xc1_ a a) s s' ->
    cEl (xc1_ a a) s u x s' u' x' -> cEl (xc1_ a a) s' u' x' s'' u'' x'' ->
    cEl (xc1_ a a) s u x s'' u'' x'' :=
  fun s s' s'' u x u' x' u'' x'' w w' w'' e H H' =>
    tr1 a a a s s' s'' u x u' x' u'' x'' w w' w'' e H H'.

Definition strE2_ (a : Ord) : forall s s' s'' u x u' x' u'' x'',
    wfs2_ a s -> wfs2_ a s' -> wfs2_ a s'' -> cU (xc2_ a a) s s' ->
    cEl (xc2_ a a) s u x s' u' x' -> cEl (xc2_ a a) s' u' x' s'' u'' x'' ->
    cEl (xc2_ a a) s u x s'' u'' x'' :=
  fun s s' s'' u x u' x' u'' x'' w w' w'' e H H' =>
    tr2 a a a s s' s'' u x u' x' u'' x'' w w' w'' e H H'.

Definition sto1_ (a : Ord) := Lto_of U1 E1 OK1 (big U1 E1 OK1 UErefl1 UEsym1 UEtrans1 a) a.
Definition sto1Coh_ (a : Ord) :=
  LtoCoh_of U1 E1 OK1 (big U1 E1 OK1 UErefl1 UEsym1 UEtrans1 a) a.

(* ---- the data ---- *)

(* a morphism of one node: the code map with the two element maps and the
   round trips, at the node's own comparison *)
Definition NodeMor (beta : Ord) : Type :=
  SMor (Ust1_ beta) (Ust2_ beta) (xcU1_ beta beta) (xcU2_ beta beta)
       (fun c : U U1 OK1 beta => wfc1_ c) (fun c : U U2 OK2 beta => wfc2_ c).

(* the whole cone of alpha, node by node.  Explicit, so that restriction is a
   projection and the stage-level dispatch is definitional. *)
Fixpoint SD (alpha : Ord) : Type :=
  match alpha with
  | ozero => unit
  | osucc beta => (NodeMor beta * SD beta)%type
  | osup T f => forall p : Pred T, (NodeMor (f p) * SD (f p))%type
  end.

(* ---- the stage-level morphism, by the dispatch ---- *)

Definition MorEmpty
  : SMor (stage1_ ozero) (stage2_ ozero) (xc1_ ozero ozero) (xc2_ ozero ozero)
         (wfs1_ ozero) (wfs2_ ozero).
Proof.
  unshelve refine (Build_SMor _ _ _ _ _ _ _ _ _ _ _ _ _); cbn; intros s; destruct s.
Defined.

Definition MorSucc (beta : Ord) (nd : NodeMor beta)
  (m0 : SMor (stage1_ beta) (stage2_ beta) (xc1_ beta beta) (xc2_ beta beta)
             (wfs1_ beta) (wfs2_ beta))
  : SMor (stage1_ (osucc beta)) (stage2_ (osucc beta))
         (xc1_ (osucc beta) (osucc beta)) (xc2_ (osucc beta) (osucc beta))
         (wfs1_ (osucc beta)) (wfs2_ (osucc beta)).
Proof.
  unshelve refine (Build_SMor _ _ _ _ _ _ _ _ _ _ _ _ _).
  - intros [c | s0] w; [exact (inl (sm_map nd c w)) | exact (inr (sm_map m0 s0 w))].
  - intros [c | s0] u x; [exact (sm_to nd c u x) | exact (sm_to m0 s0 u x)].
  - intros [c | s0] u y; [exact (sm_from nd c u y) | exact (sm_from m0 s0 u y)].
  - intros [c | s0] w; [exact (sm_sh nd c w) | exact (sm_sh m0 s0 w)].
  - intros [c | s0] w; [exact (sm_wf nd c w) | exact (sm_wf m0 s0 w)].
  - intros [c | s0] w u x; [exact (sm_rt1 nd c w u x) | exact (sm_rt1 m0 s0 w u x)].
  - intros [c | s0] w u y; [exact (sm_rt2 nd c w u y) | exact (sm_rt2 m0 s0 w u y)].
Defined.

Definition MorSup (T : etm) (f : Pred T -> Ord)
  (nd : forall p, NodeMor (f p))
  (m0 : forall p, SMor (stage1_ (f p)) (stage2_ (f p)) (xc1_ (f p) (f p))
                       (xc2_ (f p) (f p)) (wfs1_ (f p)) (wfs2_ (f p)))
  : SMor (stage1_ (osup T f)) (stage2_ (osup T f))
         (xc1_ (osup T f) (osup T f)) (xc2_ (osup T f) (osup T f))
         (wfs1_ (osup T f)) (wfs2_ (osup T f)).
Proof.
  unshelve refine (Build_SMor _ _ _ _ _ _ _ _ _ _ _ _ _).
  - intros [p [c | s0]] w;
      [exact (existT _ p (inl (sm_map (nd p) c w)))
      | exact (existT _ p (inr (sm_map (m0 p) s0 w)))].
  - intros [p [c | s0]] u x; [exact (sm_to (nd p) c u x) | exact (sm_to (m0 p) s0 u x)].
  - intros [p [c | s0]] u y; [exact (sm_from (nd p) c u y) | exact (sm_from (m0 p) s0 u y)].
  - intros [p [c | s0]] w; [exact (sm_sh (nd p) c w) | exact (sm_sh (m0 p) s0 w)].
  - intros [p [c | s0]] w; [exact (sm_wf (nd p) c w) | exact (sm_wf (m0 p) s0 w)].
  - intros [p [c | s0]] w u x;
      [exact (sm_rt1 (nd p) c w u x) | exact (sm_rt1 (m0 p) s0 w u x)].
  - intros [p [c | s0]] w u y;
      [exact (sm_rt2 (nd p) c w u y) | exact (sm_rt2 (m0 p) s0 w u y)].
Defined.

Fixpoint morOf (alpha : Ord) : SD alpha ->
  SMor (stage1_ alpha) (stage2_ alpha) (xc1_ alpha alpha) (xc2_ alpha alpha)
       (wfs1_ alpha) (wfs2_ alpha) :=
  match alpha as a return SD a ->
    SMor (stage1_ a) (stage2_ a) (xc1_ a a) (xc2_ a a) (wfs1_ a) (wfs2_ a) with
  | ozero => fun _ => MorEmpty
  | osucc beta => fun D => MorSucc beta (Datatypes.fst D) (morOf beta (Datatypes.snd D))
  | osup T f => fun D =>
      MorSup T f (fun p => Datatypes.fst (D p)) (fun p => morOf (f p) (Datatypes.snd (D p)))
  end.

(* ---- the pair statement, and the standard node ---- *)

Definition SDpres (alpha alpha' : Ord) (D : SD alpha) (D' : SD alpha') : Prop :=
  MPres (xc1_ alpha alpha') (xc2_ alpha alpha') (morOf alpha D) (morOf alpha' D').

Local Notation Mor1_ beta := (stage1_ beta) (only parsing).

Definition nodeMorOf (beta : Ord) (D0 : SD beta) (F : SDpres beta beta D0 D0)
  : NodeMor beta.
Proof.
  unshelve refine (Build_SMor _ _ _ _ _ _ _ _ _ _ _ _ _).
  - exact (fun c w => existT _ (projT1 c)
             (mapRefine (stage1_ beta) (stage2_ beta) U1 U2 E1 E2 OK1 OK2 um
                (xc1_ beta beta) (xc2_ beta beta) (wfs1_ beta) (wfs2_ beta)
                (morOf beta D0) (projT2 c) w)).
  - exact (fun c w u x =>
             elTo (stage1_ beta) (stage2_ beta) U1 U2 E1 E2 OK1 OK2 um
               (xc1_ beta beta) (xc2_ beta beta) (wfs1_ beta) (wfs2_ beta)
               (morOf beta D0) F (ssym1_ beta) (strE1_ beta) (sto1_ beta)
               (sto1Coh_ beta) (projT2 c) w u x).
  - exact (fun c w u y =>
             elFrom (stage1_ beta) (stage2_ beta) U1 U2 E1 E2 OK1 OK2 um
               (xc1_ beta beta) (xc2_ beta beta) (wfs1_ beta) (wfs2_ beta)
               (morOf beta D0) F (ssym1_ beta) (strE1_ beta) (sto1_ beta)
               (sto1Coh_ beta) (projT2 c) w u y).
  - exact (fun c w => eq_refl).
  - exact (fun c w =>
             mapRefine_wf (stage1_ beta) (stage2_ beta) U1 U2 E1 E2 OK1 OK2 um
               (xc1_ beta beta) (xc2_ beta beta) (wfs1_ beta) (wfs2_ beta)
               (morOf beta D0) F (projT2 c) w).
  - exact (fun c w u x =>
             elFrom_to (stage1_ beta) (stage2_ beta) U1 U2 E1 E2 OK1 OK2 um
               (xc1_ beta beta) (xc2_ beta beta) (wfs1_ beta) (wfs2_ beta)
               (morOf beta D0) F (ssym1_ beta) (strE1_ beta) (sto1_ beta)
               (sto1Coh_ beta) (projT2 c) w u x).
  - exact (fun c w u y =>
             elTo_from (stage1_ beta) (stage2_ beta) U1 U2 E1 E2 OK1 OK2 um
               (xc1_ beta beta) (xc2_ beta beta) (wfs1_ beta) (wfs2_ beta)
               (morOf beta D0) F (ssym1_ beta) (strE1_ beta) (strE2_ beta)
               (sto1_ beta) (sto1Coh_ beta) (projT2 c) w u y).
Defined.

(* The invariant: each node morphism of the cone IS the standard construction
   from its restriction.  One equation -- no spec up to relations, no
   transport -- and it is what lets the pair statement be proved after the
   fact, by induction, with every node formula available by conversion. *)
Definition NodeStd (beta : Ord) (nd : NodeMor beta) (D0 : SD beta) : Prop :=
  exists F : SDpres beta beta D0 D0, nd = nodeMorOf beta D0 F.

Fixpoint SDstd (alpha : Ord) : SD alpha -> Prop :=
  match alpha as a return SD a -> Prop with
  | ozero => fun _ => True
  | osucc beta => fun D =>
      NodeStd beta (Datatypes.fst D) (Datatypes.snd D) /\ SDstd beta (Datatypes.snd D)
  | osup T f => fun D =>
      forall p, NodeStd (f p) (Datatypes.fst (D p)) (Datatypes.snd (D p))
                /\ SDstd (f p) (Datatypes.snd (D p))
  end.

(* The pair statement is symmetric, by the symmetry of the two hierarchies'
   comparisons -- so the induction below proves one direction only. *)

Definition syU1 {a a'} := xsymU U1 E1 OK1 UEsym1 (alpha := a) (alpha' := a').
Definition syU2 {a a'} := xsymU U2 E2 OK2 UEsym2 (alpha := a) (alpha' := a').

Lemma SDpres_sym (alpha alpha' : Ord) (D : SD alpha) (D' : SD alpha') :
  SDpres alpha alpha' D D' -> SDpres alpha' alpha D' D.
Proof.
  intros [H1 [H2 H3]]; split; [| split].
  - intros s' w' s w e; apply syU2; apply H1; apply syU1; exact e.
  - intros s' w' s w e u y u' y' H.
    apply sy2; apply (H2 s w s' w' (syU1 _ _ e)); apply sy1; exact H.
  - intros s' w' s w e u y u' y' H.
    apply sy1; apply (H3 s w s' w' (syU1 _ _ e)); apply sy2; exact H.
Qed.

(* ---- what one node contributes to the pair statement ---- *)

Section Node.
Context (b b' : Ord) (D0 : SD b) (D0' : SD b')
        (Q : SDpres b b' D0 D0')
        (F : SDpres b b D0 D0) (F' : SDpres b' b' D0' D0').

Definition nodeU (c : U U1 OK1 b) (c' : U U1 OK1 b') (w : wfc1_ c) (w' : wfc1_ c')
  : cU (xcU1_ b b') c c' ->
    cU (xcU2_ b b') (sm_map (nodeMorOf b D0 F) c w) (sm_map (nodeMorOf b' D0' F') c' w') :=
  mapRefine_eqU (stage1_ b) (stage1_ b') (stage2_ b) (stage2_ b')
    U1 U2 E1 E2 OK1 OK2 um (xc1_ b b) (xc1_ b' b') (xc2_ b b) (xc2_ b' b')
    (xc1_ b b') (xc2_ b b') (wfs1_ b) (wfs1_ b') (wfs2_ b) (wfs2_ b')
    (morOf b D0) (morOf b' D0') Q (projT2 c) (projT2 c') w w'.

Definition nodeTo (c : U U1 OK1 b) (c' : U U1 OK1 b') (w : wfc1_ c) (w' : wfc1_ c')
  : cU (xcU1_ b b') c c' -> forall u x u' x',
    cEl (xcU1_ b b') c u x c' u' x' ->
    cEl (xcU2_ b b') (sm_map (nodeMorOf b D0 F) c w) u (sm_to (nodeMorOf b D0 F) c w u x)
        (sm_map (nodeMorOf b' D0' F') c' w') u' (sm_to (nodeMorOf b' D0' F') c' w' u' x') :=
  elTo_eqEl (stage1_ b) (stage1_ b') (stage2_ b) (stage2_ b')
    U1 U2 E1 E2 OK1 OK2 um (xc1_ b b) (xc1_ b' b') (xc2_ b b) (xc2_ b' b')
    (xc1_ b b') (xc2_ b b') (wfs1_ b) (wfs1_ b') (wfs2_ b) (wfs2_ b')
    (morOf b D0) (morOf b' D0') Q F F'
    (ssym1_ b) (ssym1_ b') (strE1_ b) (strE1_ b')
    (tr1 b b b') (tr1 b b' b') (sto1_ b) (sto1Coh_ b) (sto1_ b') (sto1Coh_ b')
    (projT2 c) (projT2 c') w w'.

Definition nodeFrom (c : U U1 OK1 b) (c' : U U1 OK1 b') (w : wfc1_ c) (w' : wfc1_ c')
  : cU (xcU1_ b b') c c' -> forall u y u' y',
    cEl (xcU2_ b b') (sm_map (nodeMorOf b D0 F) c w) u y
        (sm_map (nodeMorOf b' D0' F') c' w') u' y' ->
    cEl (xcU1_ b b') c u (sm_from (nodeMorOf b D0 F) c w u y)
        c' u' (sm_from (nodeMorOf b' D0' F') c' w' u' y') :=
  elFrom_eqEl (stage1_ b) (stage1_ b') (stage2_ b) (stage2_ b')
    U1 U2 E1 E2 OK1 OK2 um (xc1_ b b) (xc1_ b' b') (xc2_ b b) (xc2_ b' b')
    (xc1_ b b') (xc2_ b b') (wfs1_ b) (wfs1_ b') (wfs2_ b) (wfs2_ b')
    (morOf b D0) (morOf b' D0') Q F F'
    (ssym1_ b) (ssym1_ b') (strE1_ b) (strE1_ b')
    (tr1 b b b') (tr1 b b' b') (sto1_ b) (sto1Coh_ b) (sto1_ b') (sto1Coh_ b')
    (projT2 c) (projT2 c') w w'.
End Node.

(* the same three, with the node morphism given by an equation -- which is
   the form the induction below meets them in *)
Section NodeEq.
Context (b b' : Ord) (D0 : SD b) (D0' : SD b')
        (Q : SDpres b b' D0 D0')
        (nd : NodeMor b) (nd' : NodeMor b')
        (F : SDpres b b D0 D0) (F' : SDpres b' b' D0' D0')
        (HF : nd = nodeMorOf b D0 F) (HF' : nd' = nodeMorOf b' D0' F').

Lemma nodeU' (c : U U1 OK1 b) (c' : U U1 OK1 b') (w : wfc1_ c) (w' : wfc1_ c') :
  cU (xcU1_ b b') c c' -> cU (xcU2_ b b') (sm_map nd c w) (sm_map nd' c' w').
Proof. subst nd nd'; exact (nodeU b b' D0 D0' Q F F' c c' w w'). Qed.

Lemma nodeTo' (c : U U1 OK1 b) (c' : U U1 OK1 b') (w : wfc1_ c) (w' : wfc1_ c') :
  cU (xcU1_ b b') c c' -> forall u x u' x',
  cEl (xcU1_ b b') c u x c' u' x' ->
  cEl (xcU2_ b b') (sm_map nd c w) u (sm_to nd c w u x)
      (sm_map nd' c' w') u' (sm_to nd' c' w' u' x').
Proof. subst nd nd'; exact (nodeTo b b' D0 D0' Q F F' c c' w w'). Qed.

Lemma nodeFrom' (c : U U1 OK1 b) (c' : U U1 OK1 b') (w : wfc1_ c) (w' : wfc1_ c') :
  cU (xcU1_ b b') c c' -> forall u y u' y',
  cEl (xcU2_ b b') (sm_map nd c w) u y (sm_map nd' c' w') u' y' ->
  cEl (xcU1_ b b') c u (sm_from nd c w u y) c' u' (sm_from nd' c' w' u' y').
Proof. subst nd nd'; exact (nodeFrom b b' D0 D0' Q F F' c c' w w'). Qed.
End NodeEq.

(* ------------------------------------------------------------------ *)
(* THE PAIR STATEMENT.                                                 *)
(*                                                                    *)
(* Every pair fact follows from the invariant alone, by one nested      *)
(* induction: at a pair of nodes it is Codes/Mor.v's node lemma, and    *)
(* every other block of the dispatch is an instance of an induction     *)
(* hypothesis -- the comparison of a node with a code below it IS the   *)
(* comparison at the smaller pair, definitionally.                      *)
(* ------------------------------------------------------------------ *)

Lemma pres_pair : forall (alpha alpha' : Ord) (D : SD alpha) (D' : SD alpha'),
  SDstd alpha D -> SDstd alpha' D' -> SDpres alpha alpha' D D'.
Proof.
  induction alpha as [| beta IHb | T f IHf]; intros alpha'.
  - intros D D' S S'; split; [| split]; cbn; intros s; destruct s.
  - induction alpha' as [| beta' IHb' | T' f' IHf'].
    + intros D D' S S'; split; [| split]; cbn; intros s w s'; destruct s'.
    + intros [nd D0] [nd' D0'] S S'.
      pose proof S as SS; pose proof S' as SS'.
      destruct S as [[F HF] S0]; destruct S' as [[F' HF'] S0']; cbn in HF, HF'.
      split; [| split].
      * intros [c | s0] w [c' | s0'] w' e.
        -- exact (nodeU' beta beta' D0 D0' (IHb beta' D0 D0' S0 S0') nd nd' F F' HF HF'
                    c c' w w' e).
        -- exact (mpU (IHb' (nd, D0) D0' SS S0') (inl c) w s0' w' e).
        -- exact (mpU (IHb (osucc beta') D0 (nd', D0') S0 SS') s0 w (inl c') w' e).
        -- exact (mpU (IHb beta' D0 D0' S0 S0') s0 w s0' w' e).
      * intros [c | s0] w [c' | s0'] w' e u x u' x' H.
        -- exact (nodeTo' beta beta' D0 D0' (IHb beta' D0 D0' S0 S0') nd nd' F F' HF HF'
                    c c' w w' e u x u' x' H).
        -- exact (mpTo (IHb' (nd, D0) D0' SS S0') (inl c) w s0' w' e u x u' x' H).
        -- exact (mpTo (IHb (osucc beta') D0 (nd', D0') S0 SS')
                    s0 w (inl c') w' e u x u' x' H).
        -- exact (mpTo (IHb beta' D0 D0' S0 S0') s0 w s0' w' e u x u' x' H).
      * intros [c | s0] w [c' | s0'] w' e u y u' y' H.
        -- exact (nodeFrom' beta beta' D0 D0' (IHb beta' D0 D0' S0 S0') nd nd' F F' HF HF'
                    c c' w w' e u y u' y' H).
        -- exact (mpFrom (IHb' (nd, D0) D0' SS S0') (inl c) w s0' w' e u y u' y' H).
        -- exact (mpFrom (IHb (osucc beta') D0 (nd', D0') S0 SS')
                    s0 w (inl c') w' e u y u' y' H).
        -- exact (mpFrom (IHb beta' D0 D0' S0 S0') s0 w s0' w' e u y u' y' H).
    + intros [nd D0] D' S S'.
      pose proof S as SS; destruct S as [[F HF] S0]; cbn in HF.
      split; [| split].
      * intros [c | s0] w [p' [c' | s0']] w' e.
        -- destruct (S' p') as [[Fp Hp] S0p].
           exact (nodeU' beta (f' p') D0 (Datatypes.snd (D' p'))
                    (IHb (f' p') D0 _ S0 S0p) nd _ F Fp HF Hp c c' w w' e).
        -- exact (mpU (IHf' p' (nd, D0) (Datatypes.snd (D' p')) SS (proj2 (S' p')))
                    (inl c) w s0' w' e).
        -- exact (mpU (IHb (osup T' f') D0 D' S0 S') s0 w (existT _ p' (inl c')) w' e).
        -- exact (mpU (IHb (f' p') D0 (Datatypes.snd (D' p')) S0 (proj2 (S' p')))
                    s0 w s0' w' e).
      * intros [c | s0] w [p' [c' | s0']] w' e u x u' x' H.
        -- destruct (S' p') as [[Fp Hp] S0p].
           exact (nodeTo' beta (f' p') D0 (Datatypes.snd (D' p'))
                    (IHb (f' p') D0 _ S0 S0p) nd _ F Fp HF Hp c c' w w' e u x u' x' H).
        -- exact (mpTo (IHf' p' (nd, D0) (Datatypes.snd (D' p')) SS (proj2 (S' p')))
                    (inl c) w s0' w' e u x u' x' H).
        -- exact (mpTo (IHb (osup T' f') D0 D' S0 S')
                    s0 w (existT _ p' (inl c')) w' e u x u' x' H).
        -- exact (mpTo (IHb (f' p') D0 (Datatypes.snd (D' p')) S0 (proj2 (S' p')))
                    s0 w s0' w' e u x u' x' H).
      * intros [c | s0] w [p' [c' | s0']] w' e u y u' y' H.
        -- destruct (S' p') as [[Fp Hp] S0p].
           exact (nodeFrom' beta (f' p') D0 (Datatypes.snd (D' p'))
                    (IHb (f' p') D0 _ S0 S0p) nd _ F Fp HF Hp c c' w w' e u y u' y' H).
        -- exact (mpFrom (IHf' p' (nd, D0) (Datatypes.snd (D' p')) SS (proj2 (S' p')))
                    (inl c) w s0' w' e u y u' y' H).
        -- exact (mpFrom (IHb (osup T' f') D0 D' S0 S')
                    s0 w (existT _ p' (inl c')) w' e u y u' y' H).
        -- exact (mpFrom (IHb (f' p') D0 (Datatypes.snd (D' p')) S0 (proj2 (S' p')))
                    s0 w s0' w' e u y u' y' H).
  - induction alpha' as [| beta' IHb' | T' f' IHf'].
    + intros D D' S S'; split; [| split]; cbn; intros s w s'; destruct s'.
    + intros D [nd' D0'] S S'.
      pose proof S' as SS'; destruct S' as [[F' HF'] S0']; cbn in HF'.
      split; [| split].
      * intros [p [c | s0]] w [c' | s0'] w' e.
        -- destruct (S p) as [[Fp Hp] S0p].
           exact (nodeU' (f p) beta' (Datatypes.snd (D p)) D0'
                    (IHf p beta' _ D0' S0p S0') _ nd' Fp F' Hp HF' c c' w w' e).
        -- exact (mpU (IHb' D D0' S S0') (existT _ p (inl c)) w s0' w' e).
        -- exact (mpU (IHf p (osucc beta') (Datatypes.snd (D p)) (nd', D0')
                        (proj2 (S p)) SS') s0 w (inl c') w' e).
        -- exact (mpU (IHf p beta' (Datatypes.snd (D p)) D0' (proj2 (S p)) S0')
                    s0 w s0' w' e).
      * intros [p [c | s0]] w [c' | s0'] w' e u x u' x' H.
        -- destruct (S p) as [[Fp Hp] S0p].
           exact (nodeTo' (f p) beta' (Datatypes.snd (D p)) D0'
                    (IHf p beta' _ D0' S0p S0') _ nd' Fp F' Hp HF' c c' w w' e u x u' x' H).
        -- exact (mpTo (IHb' D D0' S S0')
                    (existT _ p (inl c)) w s0' w' e u x u' x' H).
        -- exact (mpTo (IHf p (osucc beta') (Datatypes.snd (D p)) (nd', D0')
                         (proj2 (S p)) SS') s0 w (inl c') w' e u x u' x' H).
        -- exact (mpTo (IHf p beta' (Datatypes.snd (D p)) D0' (proj2 (S p)) S0')
                    s0 w s0' w' e u x u' x' H).
      * intros [p [c | s0]] w [c' | s0'] w' e u y u' y' H.
        -- destruct (S p) as [[Fp Hp] S0p].
           exact (nodeFrom' (f p) beta' (Datatypes.snd (D p)) D0'
                    (IHf p beta' _ D0' S0p S0') _ nd' Fp F' Hp HF' c c' w w' e u y u' y' H).
        -- exact (mpFrom (IHb' D D0' S S0')
                    (existT _ p (inl c)) w s0' w' e u y u' y' H).
        -- exact (mpFrom (IHf p (osucc beta') (Datatypes.snd (D p)) (nd', D0')
                           (proj2 (S p)) SS') s0 w (inl c') w' e u y u' y' H).
        -- exact (mpFrom (IHf p beta' (Datatypes.snd (D p)) D0' (proj2 (S p)) S0')
                    s0 w s0' w' e u y u' y' H).
    + intros D D' S S'.
      split; [| split].
      * intros [p [c | s0]] w [p' [c' | s0']] w' e.
        -- destruct (S p) as [[Fp Hp] S0p]; destruct (S' p') as [[Fq Hq] S0q].
           exact (nodeU' (f p) (f' p') (Datatypes.snd (D p)) (Datatypes.snd (D' p'))
                    (IHf p (f' p') _ _ S0p S0q) _ _ Fp Fq Hp Hq c c' w w' e).
        -- exact (mpU (IHf' p' D (Datatypes.snd (D' p')) S (proj2 (S' p')))
                    (existT _ p (inl c)) w s0' w' e).
        -- exact (mpU (IHf p (osup T' f') (Datatypes.snd (D p)) D' (proj2 (S p)) S')
                    s0 w (existT _ p' (inl c')) w' e).
        -- exact (mpU (IHf p (f' p') (Datatypes.snd (D p)) (Datatypes.snd (D' p'))
                        (proj2 (S p)) (proj2 (S' p'))) s0 w s0' w' e).
      * intros [p [c | s0]] w [p' [c' | s0']] w' e u x u' x' H.
        -- destruct (S p) as [[Fp Hp] S0p]; destruct (S' p') as [[Fq Hq] S0q].
           exact (nodeTo' (f p) (f' p') (Datatypes.snd (D p)) (Datatypes.snd (D' p'))
                    (IHf p (f' p') _ _ S0p S0q) _ _ Fp Fq Hp Hq c c' w w' e u x u' x' H).
        -- exact (mpTo (IHf' p' D (Datatypes.snd (D' p')) S (proj2 (S' p')))
                    (existT _ p (inl c)) w s0' w' e u x u' x' H).
        -- exact (mpTo (IHf p (osup T' f') (Datatypes.snd (D p)) D' (proj2 (S p)) S')
                    s0 w (existT _ p' (inl c')) w' e u x u' x' H).
        -- exact (mpTo (IHf p (f' p') (Datatypes.snd (D p)) (Datatypes.snd (D' p'))
                         (proj2 (S p)) (proj2 (S' p'))) s0 w s0' w' e u x u' x' H).
      * intros [p [c | s0]] w [p' [c' | s0']] w' e u y u' y' H.
        -- destruct (S p) as [[Fp Hp] S0p]; destruct (S' p') as [[Fq Hq] S0q].
           exact (nodeFrom' (f p) (f' p') (Datatypes.snd (D p)) (Datatypes.snd (D' p'))
                    (IHf p (f' p') _ _ S0p S0q) _ _ Fp Fq Hp Hq c c' w w' e u y u' y' H).
        -- exact (mpFrom (IHf' p' D (Datatypes.snd (D' p')) S (proj2 (S' p')))
                    (existT _ p (inl c)) w s0' w' e u y u' y' H).
        -- exact (mpFrom (IHf p (osup T' f') (Datatypes.snd (D p)) D' (proj2 (S p)) S')
                    s0 w (existT _ p' (inl c')) w' e u y u' y' H).
        -- exact (mpFrom (IHf p (f' p') (Datatypes.snd (D p)) (Datatypes.snd (D' p'))
                           (proj2 (S p)) (proj2 (S' p'))) s0 w s0' w' e u y u' y' H).
Qed.

(* ------------------------------------------------------------------ *)
(* The canonical data, and the interface.                              *)
(* ------------------------------------------------------------------ *)

(* The step is written with the PROJECTIONS of R rather than by destructing
   it, so that `datD (osucc beta)` reduces for an arbitrary `beta`: the data
   at a successor is then the standard node morphism built from `datD beta`,
   definitionally, and `liftS_place` below is a reflexivity.  Destructing R
   would block on `dat beta` whenever beta is not a constructor -- which it
   never is in the interpretation, where the nodes are ranks of realisers. *)
Definition datSucc (beta : Ord) (R : { D : SD beta | SDstd beta D })
  : { D : SD (osucc beta) | SDstd (osucc beta) D } :=
  exist _
    (nodeMorOf beta (proj1_sig R)
       (pres_pair beta beta (proj1_sig R) (proj1_sig R)
          (proj2_sig R) (proj2_sig R)),
     proj1_sig R)
    (conj
       (ex_intro
          (fun F => nodeMorOf beta (proj1_sig R)
                      (pres_pair beta beta (proj1_sig R) (proj1_sig R)
                         (proj2_sig R) (proj2_sig R))
                    = nodeMorOf beta (proj1_sig R) F)
          (pres_pair beta beta (proj1_sig R) (proj1_sig R)
             (proj2_sig R) (proj2_sig R))
          eq_refl)
       (proj2_sig R)).

Definition datSup (T : etm) (f : Pred T -> Ord)
  (R : forall p, { D : SD (f p) | SDstd (f p) D })
  : { D : SD (osup T f) | SDstd (osup T f) D }.
Proof.
  refine (exist _ (fun p =>
            (nodeMorOf (f p) (proj1_sig (R p))
               (pres_pair (f p) (f p) _ _ (proj2_sig (R p)) (proj2_sig (R p))),
             proj1_sig (R p))) _).
  intros p; split; [cbn; eexists; reflexivity | exact (proj2_sig (R p))].
Defined.

Fixpoint dat (alpha : Ord) : { D : SD alpha | SDstd alpha D } :=
  match alpha as a return { D : SD a | SDstd a D } with
  | ozero => exist _ tt I
  | osucc beta => datSucc beta (dat beta)
  | osup T f => datSup T f (fun p => dat (f p))
  end.

Definition datD (alpha : Ord) : SD alpha := proj1_sig (dat alpha).
Definition datS (alpha : Ord) : SDstd alpha (datD alpha) := proj2_sig (dat alpha).

Definition presL (alpha alpha' : Ord)
  : SDpres alpha alpha' (datD alpha) (datD alpha') :=
  pres_pair alpha alpha' _ _ (datS alpha) (datS alpha').

(* the morphism at one node of the hierarchy: this is the lift *)
Definition ndL (beta : Ord) : NodeMor beta :=
  nodeMorOf beta (datD beta) (presL beta beta).

Definition liftC {beta} (c : U U1 OK1 beta) (w : wfc1_ c) : U U2 OK2 beta :=
  sm_map (ndL beta) c w.

Definition liftE {beta} (c : U U1 OK1 beta) (w : wfc1_ c) u
  (x : StEl (Ust1_ beta) c u) : StEl (Ust2_ beta) (liftC c w) u :=
  sm_to (ndL beta) c w u x.

Definition unliftE {beta} (c : U U1 OK1 beta) (w : wfc1_ c) u
  (y : StEl (Ust2_ beta) (liftC c w) u) : StEl (Ust1_ beta) c u :=
  sm_from (ndL beta) c w u y.

(* The lift of a SUB-STAGE element, and the one computation the interpretation
   needs of it: a component PLACED at a node below lifts to the lift of that
   component, placed at the same node.  Both sides are the cone's dispatch, so
   this is a reflexivity -- the node morphism the cone carries at a node IS
   `ndL` at that node, because `datSucc` and `datSup` build it with the same
   witness `presL` does. *)
Definition liftS {alpha} (s : St (stage1_ alpha)) (w : wfs1_ alpha s)
  : St (stage2_ alpha) :=
  sm_map (morOf alpha (datD alpha)) s w.

Lemma liftS_place (T : etm) (f : Pred T -> Ord) (p : Pred T)
  (c : U U1 OK1 (f p)) (w : wfc1_ c) :
  liftS (alpha := osup T (fun q => osucc (f q))) (existT _ p (inr (inl c))) w
  = existT _ p (inr (inl (liftC c w))).
Proof. reflexivity. Qed.

Definition liftSE {alpha} (s : St (stage1_ alpha)) (w : wfs1_ alpha s) u
  (x : StEl (stage1_ alpha) s u) : StEl (stage2_ alpha) (liftS s w) u :=
  sm_to (morOf alpha (datD alpha)) s w u x.

Definition unliftSE {alpha} (s : St (stage1_ alpha)) (w : wfs1_ alpha s) u
  (y : StEl (stage2_ alpha) (liftS s w) u) : StEl (stage1_ alpha) s u :=
  sm_from (morOf alpha (datD alpha)) s w u y.

Lemma liftSE_place (T : etm) (f : Pred T -> Ord) (p : Pred T)
  (c : U U1 OK1 (f p)) (w : wfc1_ c) u (x : StEl (Ust1_ (f p)) c u) :
  liftSE (alpha := osup T (fun q => osucc (f q))) (existT _ p (inr (inl c))) w u x
  = liftE c w u x.
Proof. reflexivity. Qed.

Lemma unliftSE_place (T : etm) (f : Pred T -> Ord) (p : Pred T)
  (c : U U1 OK1 (f p)) (w : wfc1_ c) u (y : StEl (Ust2_ (f p)) (liftC c w) u) :
  unliftSE (alpha := osup T (fun q => osucc (f q))) (existT _ p (inr (inl c))) w u y
  = unliftE c w u y.
Proof. reflexivity. Qed.

Lemma liftC_sh {beta} (c : U U1 OK1 beta) (w : wfc1_ c) : projT1 (liftC c w) = projT1 c.
Proof. exact (sm_sh (ndL beta) c w). Qed.

Lemma liftC_wf {beta} (c : U U1 OK1 beta) (w : wfc1_ c) : wfc2_ (liftC c w).
Proof. exact (sm_wf (ndL beta) c w). Qed.

Lemma liftC_eq {b b'} (c : U U1 OK1 b) (c' : U U1 OK1 b') w w' :
  ceq U1 E1 OK1 c c' -> ceq U2 E2 OK2 (liftC c w) (liftC c' w').
Proof.
  exact (nodeU b b' (datD b) (datD b') (presL b b') (presL b b) (presL b' b')
           c c' w w').
Qed.

Lemma liftE_eq {b b'} (c : U U1 OK1 b) (c' : U U1 OK1 b') w w' :
  ceq U1 E1 OK1 c c' -> forall u x u' x',
  cel U1 E1 OK1 c u x c' u' x' ->
  cel U2 E2 OK2 (liftC c w) u (liftE c w u x) (liftC c' w') u' (liftE c' w' u' x').
Proof.
  exact (nodeTo b b' (datD b) (datD b') (presL b b') (presL b b) (presL b' b')
           c c' w w').
Qed.

Lemma unliftE_eq {b b'} (c : U U1 OK1 b) (c' : U U1 OK1 b') w w' :
  ceq U1 E1 OK1 c c' -> forall u y u' y',
  cel U2 E2 OK2 (liftC c w) u y (liftC c' w') u' y' ->
  cel U1 E1 OK1 c u (unliftE c w u y) c' u' (unliftE c' w' u' y').
Proof.
  exact (nodeFrom b b' (datD b) (datD b') (presL b b') (presL b b) (presL b' b')
           c c' w w').
Qed.

Lemma unliftE_liftE {b} (c : U U1 OK1 b) w u x :
  cel U1 E1 OK1 c u (unliftE c w u (liftE c w u x)) c u x.
Proof. exact (sm_rt1 (ndL b) c w u x). Qed.

Lemma liftE_unliftE {b} (c : U U1 OK1 b) w u y :
  cel U2 E2 OK2 (liftC c w) u (liftE c w u (unliftE c w u y)) (liftC c w) u y.
Proof. exact (sm_rt2 (ndL b) c w u y). Qed.
End Hierarchy.

(* ------------------------------------------------------------------ *)
(* THE INSTANCE: level k into level S k.                               *)
(*                                                                    *)
(* The two universe parameters differ only at m = k, and a level-k code *)
(* cannot mention that level, so the map is the sum's injection -- one  *)
(* constructor, where v1 had to transport along `lU_spec`, an equality  *)
(* of TYPES proved by induction on the level.                           *)
(* ------------------------------------------------------------------ *)

Lemma lOK_lt (k m : nat) : lOK (lvl k) m <-> m < k.
Proof.
  destruct k as [| j]; cbn; split; intros H; [destruct H | lia | exact H | exact H].
Qed.

Definition lOK_lt1 (k m : nat) : lOK (lvl k) m -> m < k := proj1 (lOK_lt k m).
Definition lOK_lt2 (k m : nat) : m < k -> lOK (lvl k) m := proj2 (lOK_lt k m).

Definition lvlTo (k m : nat) (u : etm) (o : lOK (lvl k) m) (x : lU (lvl k) m u)
  : lU (lvl (S k)) m u.
Proof.
  refine (inr (x, _)); pose proof (lOK_lt1 k m o); lia.
Defined.

Definition lvlFrom (k m : nat) (u : etm) (o : lOK (lvl k) m) (y : lU (lvl (S k)) m u)
  : lU (lvl k) m u.
Proof.
  cbn in y; destruct y as [[F e] | [x ne]];
    [exfalso; pose proof (lOK_lt1 k m o); lia | exact x].
Defined.

Definition lvlOK (k m : nat) (o : lOK (lvl k) m) : lOK (lvl (S k)) m.
Proof. apply lOK_lt2; pose proof (lOK_lt1 k m o); lia. Defined.

Definition lvlUM (k : nat)
  : UMor (lU (lvl k)) (lU (lvl (S k))) (lUEq (lvl k)) (lUEq (lvl (S k)))
         (lOK (lvl k)) (lOK (lvl (S k))).
Proof.
  refine (Build_UMor _ _ _ _ _ _ (lvlOK k) (lvlTo k) (lvlFrom k) _ _ _ _).
  - intros m o u x m' o' u' x' H; exact H.
  - intros m o u y m' o' u' y' H.
    revert H; cbn in y, y' |- *.
    destruct y as [[F e] | [x ne]]; [exfalso; pose proof (lOK_lt1 k m o); lia |].
    destruct y' as [[F' e'] | [x' ne']];
      [intros []
      | cbn; exact (fun h => h)].
  - intros m o u y; cbn in y |- *.
    destruct y as [[F e] | [x ne]]; [exfalso; pose proof (lOK_lt1 k m o); lia |].
    cbn; apply (lrefl (lvl k)).
  - intros m o u x; cbn; apply (lrefl (lvl k)).
Defined.

(* the level-k hierarchy's structure, as the generic construction wants it *)
Local Notation LA k := (lU (lvl k)) (only parsing).
Local Notation LE k := (lUEq (lvl k)) (only parsing).
Local Notation LO k := (lOK (lvl k)) (only parsing).

Definition liftCode (k : nat) {beta : Ord} (c : Code k beta) (w : wfn c)
  : Code (S k) beta :=
  liftC (LA k) (LA (S k)) (LE k) (LE (S k)) (LO k) (LO (S k)) (lvlUM k)
    (lrefl (lvl k)) (lsym (lvl k)) (ltrans (lvl k))
    (lrefl (lvl (S k))) (lsym (lvl (S k))) (ltrans (lvl (S k))) c w.

Definition liftEl (k : nat) {beta : Ord} (c : Code k beta) (w : wfn c) u
  (x : StEl (Ust (LA k) (LO k) beta) c u)
  : StEl (Ust (LA (S k)) (LO (S k)) beta) (liftCode k c w) u :=
  liftE (LA k) (LA (S k)) (LE k) (LE (S k)) (LO k) (LO (S k)) (lvlUM k)
    (lrefl (lvl k)) (lsym (lvl k)) (ltrans (lvl k))
    (lrefl (lvl (S k))) (lsym (lvl (S k))) (ltrans (lvl (S k))) c w u x.

(* The same on a SUB-STAGE element, with the one computation the
   interpretation needs of it: a component PLACED at a node below lifts to the
   lift of that component, placed at the same node.  See `liftS_place`. *)
Definition liftSub (k : nat) {alpha : Ord} (s : LSub (lvl k) alpha)
  (w : wfsub (LA k) (LE k) (LO k) alpha s) : LSub (lvl (S k)) alpha :=
  liftS (LA k) (LA (S k)) (LE k) (LE (S k)) (LO k) (LO (S k)) (lvlUM k)
    (lrefl (lvl k)) (lsym (lvl k)) (ltrans (lvl k))
    (lrefl (lvl (S k))) (lsym (lvl (S k))) (ltrans (lvl (S k))) s w.

Lemma liftSub_place (k : nat) (T : etm) (f : Pred T -> Ord) (p : Pred T)
  (c : Code k (f p)) (w : wfn c) :
  liftSub k (alpha := osup T (fun q => osucc (f q))) (existT _ p (inr (inl c))) w
  = existT _ p (inr (inl (liftCode k c w))).
Proof. reflexivity. Qed.

Definition liftSubEl (k : nat) {alpha : Ord} (s : LSub (lvl k) alpha)
  (w : wfsub (LA k) (LE k) (LO k) alpha s) u
  (x : StEl (stage (LA k) (LO k) alpha) s u)
  : StEl (stage (LA (S k)) (LO (S k)) alpha) (liftSub k s w) u :=
  liftSE (LA k) (LA (S k)) (LE k) (LE (S k)) (LO k) (LO (S k)) (lvlUM k)
    (lrefl (lvl k)) (lsym (lvl k)) (ltrans (lvl k))
    (lrefl (lvl (S k))) (lsym (lvl (S k))) (ltrans (lvl (S k))) s w u x.


Lemma liftSubEl_place (k : nat) (T : etm) (f : Pred T -> Ord) (p : Pred T)
  (c : Code k (f p)) (w : wfn c) u (x : StEl (Ust (LA k) (LO k) (f p)) c u) :
  liftSubEl k (alpha := osup T (fun q => osucc (f q)))
    (existT _ p (inr (inl c))) w u x = liftEl k c w u x.
Proof. reflexivity. Qed.


Lemma liftCode_sh (k : nat) {beta} (c : Code k beta) (w : wfn c) :
  LSh (liftCode k c w) = LSh c.
Proof.
  exact (liftC_sh (LA k) (LA (S k)) (LE k) (LE (S k)) (LO k) (LO (S k)) (lvlUM k)
           (lrefl (lvl k)) (lsym (lvl k)) (ltrans (lvl k))
           (lrefl (lvl (S k))) (lsym (lvl (S k))) (ltrans (lvl (S k))) c w).
Qed.

Lemma liftCode_wf (k : nat) {beta} (c : Code k beta) (w : wfn c) :
  wfn (liftCode k c w).
Proof.
  exact (liftC_wf (LA k) (LA (S k)) (LE k) (LE (S k)) (LO k) (LO (S k)) (lvlUM k)
           (lrefl (lvl k)) (lsym (lvl k)) (ltrans (lvl k))
           (lrefl (lvl (S k))) (lsym (lvl (S k))) (ltrans (lvl (S k))) c w).
Qed.

Lemma liftCode_ceq (k : nat) {b b'} (c : Code k b) (c' : Code k b') w w' :
  ceqn c c' -> ceqn (liftCode k c w) (liftCode k c' w').
Proof.
  exact (liftC_eq (LA k) (LA (S k)) (LE k) (LE (S k)) (LO k) (LO (S k)) (lvlUM k)
           (lrefl (lvl k)) (lsym (lvl k)) (ltrans (lvl k))
           (lrefl (lvl (S k))) (lsym (lvl (S k))) (ltrans (lvl (S k))) c c' w w').
Qed.

Lemma liftEl_cel (k : nat) {b b'} (c : Code k b) (c' : Code k b') w w' :
  ceqn c c' -> forall u x u' x',
  cel (LA k) (LE k) (LO k) c u x c' u' x' ->
  cel (LA (S k)) (LE (S k)) (LO (S k))
    (liftCode k c w) u (liftEl k c w u x) (liftCode k c' w') u' (liftEl k c' w' u' x').
Proof.
  exact (liftE_eq (LA k) (LA (S k)) (LE k) (LE (S k)) (LO k) (LO (S k)) (lvlUM k)
           (lrefl (lvl k)) (lsym (lvl k)) (ltrans (lvl k))
           (lrefl (lvl (S k))) (lsym (lvl (S k))) (ltrans (lvl (S k))) c c' w w').
Qed.

(* ------------------------------------------------------------------ *)
(* The lift of a whole universe family: blueprint Lemma 7.7.           *)
(* Every field travels -- the shadow by liftCode_sh, the two layer-1    *)
(* equations by cumulativity, well-formedness and coherence by the two  *)
(* lemmas above.  v1 needed a fifth field (uf_idp) and the naturality   *)
(* square of LiftIso.v; neither exists here.                            *)
(* ------------------------------------------------------------------ *)

Definition famLift (k : nat) (n n' : nat) (Hn : n <= n') (u : etm)
  (F : UFam (lvl k) n u) : UFam (lvl (S k)) n' u.
Proof.
  refine (Build_UFam (lvl (S k)) n' u
            (fun v h pf => liftCode k (uf_c F v h pf) (uf_wf F v h pf)) _ _ _ _).
  - exact (eqty_cumul n n' u u Hn (uf_ty F)).
  - intros v h pf; rewrite liftCode_sh.
    exact (eqty_cumul n n' _ u Hn (uf_sh F v h pf)).
  - intros v h pf; apply liftCode_wf.
  - intros v h pf v' h' pf'; apply liftCode_ceq; exact (uf_coh F v h pf v' h' pf').
Defined.

Lemma famLift_c (k n n' : nat) (Hn : n <= n') u (F : UFam (lvl k) n u) v h pf :
  uf_c (famLift k n n' Hn u F) v h pf = liftCode k (uf_c F v h pf) (uf_wf F v h pf).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The lift against the coercion.                                      *)
(*                                                                    *)
(* v1's LiftIso.v had to carry a naturality square through every clause *)
(* of the hierarchy, because its Pi clause was stated in terms of the   *)
(* transport a code carries.  Here the square is a corollary: the lift  *)
(* of a coerced element and the coercion of a lifted one are both       *)
(* related to the lift of the original, so symmetry and transitivity at *)
(* level S k put them together.                                        *)
(* ------------------------------------------------------------------ *)

Lemma liftEl_xto (k : nat) {b b'} (c : Code k b) (c' : Code k b') (w : wfn c) (w' : wfn c')
  (e : ceqn c c') u x :
  cel (LA (S k)) (LE (S k)) (LO (S k))
    (liftCode k c' w') u
    (liftEl k c' w' u
       (xto (LA k) (LE k) (LO k) (lrefl (lvl k)) (lsym (lvl k)) (ltrans (lvl k))
          c c' w w' e u x))
    (liftCode k c' w') u
    (xto (LA (S k)) (LE (S k)) (LO (S k)) (lrefl (lvl (S k))) (lsym (lvl (S k)))
       (ltrans (lvl (S k))) (liftCode k c w) (liftCode k c' w')
       (liftCode_wf k c w) (liftCode_wf k c' w') (liftCode_ceq k c c' w w' e) u
       (liftEl k c w u x)).
Proof.
  eapply (xtrE (LA (S k)) (LE (S k)) (LO (S k)) (lrefl (lvl (S k))) (lsym (lvl (S k)))
            (ltrans (lvl (S k))) (liftCode k c' w') (liftCode k c w) (liftCode k c' w'));
    [ apply liftCode_wf | apply liftCode_wf | apply liftCode_wf
    | apply (nsymU (LA (S k)) (LE (S k)) (LO (S k)) (lsym (lvl (S k))));
      apply liftCode_ceq; exact e
    | (* the lift of the coerced element is related to the lift of the original *)
      apply (nsym (LA (S k)) (LE (S k)) (LO (S k)) (lsym (lvl (S k))));
      apply (liftEl_cel k c c' w w' e);
      apply (xto_coh (LA k) (LE k) (LO k) (lrefl (lvl k)) (lsym (lvl k))
               (ltrans (lvl k)) c c' w w' e)
    | (* and so is the coercion of the lift *)
      apply (xto_coh (LA (S k)) (LE (S k)) (LO (S k)) (lrefl (lvl (S k)))
               (lsym (lvl (S k))) (ltrans (lvl (S k)))) ].
Qed.

(* ------------------------------------------------------------------ *)
(* And the way back down.                                              *)
(*                                                                    *)
(* `SMor` is an EQUIVALENCE -- sm_from with both round trips -- so the  *)
(* lift of codes is reversible on elements.  The eliminators need this: *)
(* a term at an annotated level d + j is read in a d-fold lift of the   *)
(* level-j family, and its elimination happens at level j.             *)
(* ------------------------------------------------------------------ *)

Definition unliftEl (k : nat) {beta : Ord} (c : Code k beta) (w : wfn c) u
  (y : StEl (Ust (LA (S k)) (LO (S k)) beta) (liftCode k c w) u)
  : StEl (Ust (LA k) (LO k) beta) c u :=
  unliftE (LA k) (LA (S k)) (LE k) (LE (S k)) (LO k) (LO (S k)) (lvlUM k)
    (lrefl (lvl k)) (lsym (lvl k)) (ltrans (lvl k))
    (lrefl (lvl (S k))) (lsym (lvl (S k))) (ltrans (lvl (S k))) c w u y.

Definition unliftSubEl (k : nat) {alpha : Ord} (s : LSub (lvl k) alpha)
  (w : wfsub (LA k) (LE k) (LO k) alpha s) u
  (y : StEl (stage (LA (S k)) (LO (S k)) alpha) (liftSub k s w) u)
  : StEl (stage (LA k) (LO k) alpha) s u :=
  unliftSE (LA k) (LA (S k)) (LE k) (LE (S k)) (LO k) (LO (S k)) (lvlUM k)
    (lrefl (lvl k)) (lsym (lvl k)) (ltrans (lvl k))
    (lrefl (lvl (S k))) (lsym (lvl (S k))) (ltrans (lvl (S k))) s w u y.

Lemma unliftSubEl_place (k : nat) (T : etm) (f : Pred T -> Ord) (p : Pred T)
  (c : Code k (f p)) (w : wfn c) u
  (y : StEl (Ust (LA (S k)) (LO (S k)) (f p)) (liftCode k c w) u) :
  unliftSubEl k (alpha := osup T (fun q => osucc (f q)))
    (existT _ p (inr (inl c))) w u y = unliftEl k c w u y.
Proof. reflexivity. Qed.

Lemma unliftEl_cel (k : nat) {b b'} (c : Code k b) (c' : Code k b') w w' :
  ceqn c c' -> forall u y u' y',
  cel (LA (S k)) (LE (S k)) (LO (S k))
    (liftCode k c w) u y (liftCode k c' w') u' y' ->
  cel (LA k) (LE k) (LO k)
    c u (unliftEl k c w u y) c' u' (unliftEl k c' w' u' y').
Proof.
  exact (unliftE_eq (LA k) (LA (S k)) (LE k) (LE (S k)) (LO k) (LO (S k)) (lvlUM k)
           (lrefl (lvl k)) (lsym (lvl k)) (ltrans (lvl k))
           (lrefl (lvl (S k))) (lsym (lvl (S k))) (ltrans (lvl (S k))) c c' w w').
Qed.

Lemma unliftEl_liftEl (k : nat) {b} (c : Code k b) w u x :
  cel (LA k) (LE k) (LO k) c u (unliftEl k c w u (liftEl k c w u x)) c u x.
Proof.
  exact (unliftE_liftE (LA k) (LA (S k)) (LE k) (LE (S k)) (LO k) (LO (S k)) (lvlUM k)
           (lrefl (lvl k)) (lsym (lvl k)) (ltrans (lvl k))
           (lrefl (lvl (S k))) (lsym (lvl (S k))) (ltrans (lvl (S k))) c w u x).
Qed.

Lemma liftEl_unliftEl (k : nat) {b} (c : Code k b) w u y :
  cel (LA (S k)) (LE (S k)) (LO (S k))
    (liftCode k c w) u (liftEl k c w u (unliftEl k c w u y)) (liftCode k c w) u y.
Proof.
  exact (liftE_unliftE (LA k) (LA (S k)) (LE k) (LE (S k)) (LO k) (LO (S k)) (lvlUM k)
           (lrefl (lvl k)) (lsym (lvl k)) (ltrans (lvl k))
           (lrefl (lvl (S k))) (lsym (lvl (S k))) (ltrans (lvl (S k))) c w u y).
Qed.
