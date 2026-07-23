From Stdlib Require Import Arith.
From Stdlib Require Import List.
From elpi Require Import elpi.
From mathcomp Require Import all_ssreflect.
Require Import calc_no_math_comp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma eq_bigr_no_pred:
  forall [R:Type] [idx: R] [op: R->R->R] [I:Type] [r:seq I] [F1:I->R] (F2:I->R),
    (forall i:I, F1 i = F2 i) -> 
      \big[op/idx]_(i <- r)  F1 i =
      \big[op/idx]_(i <- r)  F2 i.
Proof.
  intros R idx op I r F1 F2 H.
  apply eq_bigr.
  intros i H1.
  apply H.
Qed.

Lemma eq_big_all:
  forall [R:Type] [idx:R] [op: R->R->R] [I:eqType] [r:seq I] [P1:pred I] (P2:pred I) [F1:I->R] (F2:I->R),
  {in r, P1 =1 P2} ->
  {in r, forall i:I, P1 i -> F1 i = F2 i} ->
  \big[op/idx]_(i <- r | P1 i)  F1 i = \big[op/idx]_(i <- r | P2 i)  F2 i.
Proof.
  intros R idx op I r P1 P2 F1 F2 H1 H2.
  transitivity (\big[op/idx]_(i <- r | (i \in r) && P1 i)  F1 i).
  apply big_seq_cond.
  transitivity ((\big[op/idx]_(i <- r | (i \in r) && P2 i)  F2 i)).
  apply eq_big.
  intro i.
  apply Bool.eq_true_iff_eq.
  firstorder.
  apply andb_true_intro.
  apply conj.
  apply andb_prop in H.
  destruct H.
  assumption.
  apply andb_prop in H.
  destruct H.
  transitivity (P1 i).
  2:assumption.
  rewrite H1.
  reflexivity.
  apply H.
  apply andb_true_intro.
  apply conj.
  apply andb_prop in H.
  destruct H.
  assumption.
  apply andb_prop in H.
  destruct H.
  transitivity (P1 i).
  reflexivity.
  rewrite H1.
  apply H0.
  apply H.
  intros i H3.
  apply H2.
  apply andb_prop in H3.
  destruct H3.
  apply H.
  apply andb_prop in H3.
  destruct H3.
  apply H0.
  apply Logic.eq_sym.
  apply big_seq_cond.
Qed.

Elpi Accumulate relations.db lp:{{

  step_by_context_aux ({{ \big[ lp:Op / lp:Idx ]_( i <- lp:L) lp:(F1 i) }} as X1) {{ \big[ lp:Op / lp:Idx ]_( i <- lp:L) lp:(F2 i) }} Y1 Y2 _ P'' J :-
    X1 = {{ @bigop.body lp:B _ _ _ lp:{{ fun N A _}} }},
    coq.typecheck Idx B ok,
    @pi-decl N A x\ (
      instantiate-replacement N A x Y1 Y2 (Y1' x) (Y2' x),
      coq.string->name "H" H0,
      fresh-name H0 {{lp:x \in lp:L}} H,
      @pi-decl H {{lp:x \in lp:L}} h\ (
        step_by_context_aux (F1 x) (F2 x) (Y1' x) (Y2' x) _ (Prf x h) IF
      )
    ),
    J is IF,
    transform_proof J X1 {{eq_big_seq lp:{{fun N A F2}} lp:{{fun N A x\ (fun H {{lp:x \in lp:L}} h\ Prf x h)}}}} P',
    coq.elaborate-skeleton P' _ P'' ok.

  step_by_context_aux ({{ \big[ lp:Op / lp:Idx ]_( i <- lp:L| lp:(P1 i)) lp:(F1 i) }} as X1) {{ \big[ lp:Op / lp:Idx ]_( i <- lp:L | lp:(P2 i)) lp:(F2 i) }} Y1 Y2 _ P'' J :-
    X1 = {{ @bigop.body lp:B _ _ _ lp:{{ fun N A _}} }},
    coq.typecheck Idx B ok,
    @pi-decl N A x\ (
      instantiate-replacement N A x Y1 Y2 (Y1' x) (Y2' x),
      coq.string->name "H" H0,
      fresh-name H0 {{lp:x \in lp:L}} H,
      @pi-decl H {{lp:x \in lp:L}} h\ (
        step_by_context_aux (P1 x) (P2 x) (Y1' x) (Y2' x) _ (PP x h) IP,
        fresh-name H0 (P1 x) H',
        @pi-decl H' (P1 x) h'\ (
          step_by_context_aux (F1 x) (F2 x) (Y1' x) (Y2' x) _ (PF x h h') IF
        )
      )
    ),
    J is IP + IF,
    transform_proof J X1 {{eq_big_all lp:{{fun N A x\ (fun H {{lp:x \in lp:L}} h\ PP x h)}} lp:{{fun N A x\ (fun H {{lp:x \in lp:L}} h\ (fun H' (P1 x) h'\ PF x h h'))}}}} P',
    coq.elaborate-skeleton P' _ P'' ok.

  step_by_context_aux ({{ \big[ lp:Op / lp:Idx ]_( i <- lp:L) lp:(F1 i) }} as X1) {{ \big[ lp:Op / lp:Idx ]_( i <- lp:L) lp:(F2 i) }} Y1 Y2 _ P'' J :-
    X1 = {{ @bigop.body lp:B _ _ _ lp:{{ fun N A _}} }},
    coq.typecheck Idx B ok,
    @pi-decl N A x\ (
        instantiate-replacement N A x Y1 Y2 (Y1' x) (Y2' x),
        step_by_context_aux (F1 x) (F2 x) (Y1' x)  (Y2' x) _ (Prf x) IF
    ),
    J is IF,
    transform_proof J X1 {{eq_bigr_no_pred lp:{{fun N A x\ Prf x }}}} P',
    coq.elaborate-skeleton P' _ P'' ok.

  step_by_context_aux ({{ \big[ lp:Op / lp:Idx ]_( i <- lp:L| lp:(P1 i)) lp:(F1 i) }} as X1) {{ \big[ lp:Op / lp:Idx ]_( i <- lp:L | lp:(P2 i)) lp:(F2 i) }} Y1 Y2 _ P'' J :-
    X1 = {{ @bigop.body lp:B _ _ _ lp:{{ fun N A _}} }},
    coq.typecheck Idx B ok,
    @pi-decl N A x\ (
      coq.string->name "H" H0,
      fresh-name H0 (P x) H,
      instantiate-replacement N A x Y1 Y2 (Y1' x) (Y2' x),
      step_by_context_aux (P1 x) (P2 x) (Y1' x) (Y2' x) _ (PP x) IP,
      @pi-decl H (P1 x) h\ (
        step_by_context_aux (F1 x) (F2 x) (Y1' x) (Y2' x) _ (PF x h) IF
      )
    ),
    J is IF + IP,
    transform_proof J X1 {{eq_big lp:{{fun N A P2}} lp:{{fun N A F2}} lp:{{fun N A PP}} lp:{{fun N A x\ (fun H (P x) h\ PF x h)}}}} P',
    coq.elaborate-skeleton P' _ P'' ok.
}}.