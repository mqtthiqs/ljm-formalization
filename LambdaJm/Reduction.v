
Require Import Metalib.Metatheory.
Require Import LambdaJm.Syntax.

Import LambdaJmNotations.

(***********************************************************************)
(** * Append operation *)
(***********************************************************************)

Fixpoint app_args_args (a1:gmargs) (a2:gmargs) {struct a1}: gmargs :=
  match a1 with
  | (args t l c)  => args t l (app_cont_args c a2)
  end
with app_cont_args (c:cont) (a:gmargs) : cont :=
  match c with
  | cabs v =>
    cabs (app_term_x_args v a)
  end
with app_term_x_args (v:term) (a:gmargs) {struct v}: term :=
  match v with
  | (app (var_b 0) a1) => if (testINargs_rec 0 a1)   (* if 0 is in a1 *)
                         then app v a
                         else app (var_b 0) (app_args_args a1 a)
  | _                  => app v a
  end.

Fixpoint app_term_args (t:term) (a:gmargs) {struct t}: term :=
  match t with
  | (app t1 a1)   => app t1 (app_args_args a1 a)
  | _             => app t a
  end.

Fixpoint app_term_cont (t:term) (c:cont): term :=
  match c with
  | (cabs v)  => open_term_wrt_term v t     
  end.

Fixpoint app_cont_cont (c1:cont) (c2:cont) {struct c1}: cont :=
  match c1 with
  | (cabs (var_b 0))  => c2
  | (cabs (app (var_b 0) (args u l c))) =>
              if (testINargs_rec 0 (args u l c))
              then  cabs (app_term_cont (app (var_b 0) (args u l c)) c2)
              else  cabs (app (var_b 0) (args u l (app_cont_cont c c2)))
              
  | (cabs v)  => cabs (app_term_cont v c2)
  end.

Fixpoint app_alist_alist (l1:alist) (l2:alist): alist :=
  match l1 with
  | anil          => l2
  | (acons t l3)  => acons t (app_alist_alist l3 l2)
  end.

Notation "l1 +@+ l2"    := (app_alist_alist l1 l2) (at level 0, right associativity).


(* Mail do JES:
Na prova do Lema 2 no apêndice, penúltimo caso (v = x(u,l,c) e x \notin u,l,c), 
usa-se IH relativa à continuação c, mas esta continuação c não é sub-expressão imediata 
do termo v. Obviamente que isto não põe em causa a prova informal, porque c é de facto 
"menor" que v. Mas isto põe, de facto, um problema à formalização, porque a prova dá 
2 "saltos" num único "salto": da continuação c para o termo v via o argumento (u,l,c). 

Esta passagem silenciosa pelo argumento (u,l,c) indica que, implicitamente, há um terceiro 
item no lema 2 relativo a argumentos: a'@a = a' @ (z)za, se z \notin a. Mas a operação a'@c 
não está (ainda) definida. A def. seria óbvia ( (u,l,c)@c' = (u,l,c@c') ) e permitiria 
simplificar a Def 1, item 5. A minha sensação é que seria acertado introduzir a nova def.

Porém, é possível continuar a viver (e fazer a prova do Lema 2 em Coq) sem introduzir essa
 definição. Para isso, basta enunciar o terceiro item do Lema 2 assim

Q(a):= para todo u,l,c,z,a' [ se (a=(u,l,c) e z \notin a') então a@a' = (u,l,c(z)za') ]

Já estou a dar o nome Q a este predicado. Este predicado substitui o predicado Q(a)=true 
que estávamos a usar na prova formal. Esta continua a seguir o mesmo princípio de indução. 
Surge uma nova obrigação de prova relativa ao único construtor de args, que deve seguir 
imediatamente pela hipótese de indução relativa à continuação do argumento, usando o item 2 
da Def 1. Finalmente, de volta ao caso v = x(u,l,c) e x \notin u,l,c, há uma ligeira 
alteração na prova do apêndice: não se chama o item 2 da Def 1, aplica-se imediatamente
 a IH relativa a a=(u,l,c).
*)
Lemma app_coherence :
  (forall v a, (testINargs_rec 0 a = false) ->
          (cabs (app_term_x_args v a)) = app_cont_cont (cabs v) (cabs (app (var_b 0) a))) /\
  (forall a1 u l c a, (testINargs_rec 0 a = false) /\ a1 = (args u l c) ->
              (app_args_args a1 a) = (args u l (app_cont_cont c (cabs (app (var_b 0) a)))))
  /\ (forall l:alist, True) /\
  (forall c a, (testINargs_rec 0 a = false) ->                        
          app_cont_args c a = app_cont_cont c (cabs (app (var_b 0) a))).
Proof.
  apply (term_gmargs_alist_cont_mutind 
           (fun v => (forall a, (testINargs_rec 0 a = false) ->
                     (cabs (app_term_x_args v a)) = app_cont_cont (cabs v) (cabs (app (var_b 0) a))))
           (fun a1 => (forall u l c a, (testINargs_rec 0 a = false) /\ a1 = (args u l c) ->
                      (app_args_args a1 a) = (args u l (app_cont_cont c (cabs (app (var_b 0) a))))))
           (fun l => True)
           (fun c => (forall a, (testINargs_rec 0 a = false) ->
                      app_cont_args c a = app_cont_cont c (cabs (app (var_b 0) a)))) ).
  - intros n a H. simpl. destruct n.
    + reflexivity.
    + cbn; repeat f_equal; symmetry; apply testIN_open_rec; assumption.
  - intros x a H. cbn; repeat f_equal; symmetry; apply testIN_open_rec; assumption.
  - intros t H a H0. cbn; repeat f_equal; symmetry; apply testIN_open_rec; assumption.
  - intros t H a H0 a0 H1. simpl. destruct t. 
    + destruct n.
      * destruct (testINargs_rec 0 a) eqn:Ht.
        -- destruct a. simpl in Ht. rewrite Ht. f_equal.
           cbn; repeat f_equal; symmetry; apply testIN_open_rec; assumption. 
        --  destruct a.  simpl in Ht. rewrite Ht. repeat f_equal. apply H0. split.
            ++ assumption.
            ++ reflexivity.               
      * cbn; repeat f_equal; symmetry; apply testIN_open_rec; assumption.
    + cbn; repeat f_equal; symmetry; apply testIN_open_rec; assumption.
    + cbn; repeat f_equal; symmetry; apply testIN_open_rec; assumption.
    + cbn; repeat f_equal; symmetry; apply testIN_open_rec; assumption.
  - intros u H l H0 c H1 u0 l0 c0 a H2. destruct H2.
    inversion H3. simpl. repeat f_equal. rewrite <- H7.  apply H1. assumption.
  - trivial.
  - trivial.
  - intros v H a H0. assert (H1 :cabs (app_term_x_args v a) = app_cont_args (cabs v) a).
    + simpl. reflexivity.
    + apply H. assumption.
Qed.




(***********************************************************************)
(** * Reduction rules *)
(***********************************************************************)

(** Note that we use [open] instead of
    substitution --- no variable names are involved.

    Note also the hypotheses in [..._rule] that ensure that the relation holds
    only for locally closed terms.  *)

Inductive beta1T : term -> term -> Prop :=
 | beta1_rule : forall (t u v:term),
     lcT (abs t) ->
     lcT u ->
     lcC (cabs v) ->
     beta1T (app (abs t) (args u anil (cabs v))) (openT v (openT t u)).

Inductive beta2T : term -> term -> Prop :=
 | beta2_rule : forall (t u u':term) (l:alist) (c:cont),
     lcT (abs t) ->
     lcT u ->
     lcT u' ->
     lcL l ->
     lcC c ->
     beta2T (app (abs t) (args u (acons u' l) c)) (app (openT t u) (args u' l c)).

Inductive betaT : term -> term -> Prop :=
 | beta_rule1 : forall (t t':term),
     beta1T t t' -> betaT t t'
 | beta_rule2 : forall (t t':term),
     beta2T t t' -> betaT t t'.

Inductive piT : term -> term -> Prop :=
 | pi_rule : forall (t:term) (a a':gmargs),
     lcT t ->
     lcA a ->
     lcA a' ->
     piT (app (app t a) a') (app t (app_args_args a a')).

Inductive betapiT : term -> term -> Prop :=
 | rule_beta : forall (t t':term),
     betaT t t' -> betapiT t t'
 | rule_pi : forall (t t':term),
     piT t t' -> betapiT t t'.

Inductive muA : gmargs -> gmargs -> Prop :=
| mu_rule : forall (u u':term) (l l':alist) (c':cont),
     lcT u ->
     lcT u' ->
     lcL l ->
     lcL l' ->
     lcC c' ->
     muA (args u l (cabs (app (var_b 0) (args u' l' c'))))
         (args u (l +@+ (u':::l')) c').

Lemma beta1_lc : forall e1 e2, beta1T e1 e2 -> lcT e1.
Proof. intros e1 e2 H. inversion H; auto. Qed.

Lemma beta2_lc : forall e1 e2, beta2T e1 e2 -> lcT e1.
Proof. intros e1 e2 H. inversion H; auto. Qed.

Lemma beta_lc : forall e1 e2, betaT e1 e2 -> lcT e1.
Proof.
  intros e1 e2 H. inversion H; auto.
  - apply (beta1_lc e1 e2). assumption.
  - apply (beta2_lc e1 e2). assumption.
Qed.

(* Lemma pi_lc : forall e1 e2, piT e1 e2 -> lcT e1. *)
(* Proof. intros e1 e2 H. inversion H; auto. Qed. *)

(* Lemma betapi_lc : forall e1 e2, betapiT e1 e2 -> lcT e1. *)
(* Proof. *)
(*   intros e1 e2 H. inversion H; auto. *)
(*   - apply (beta_lc e1 e2). assumption. *)
(*   - apply (pi_lc e1 e2). assumption. *)
(* Qed. *)


(***********************************************************************)
(** * Closures *)
(***********************************************************************)

(** WIP: mjf  *)


(**************************
 * Reflexive closures
 **************************)

(* Reflexive closure of R (in terms) *)
Inductive rcRTT (R : term -> term -> Prop) : term -> term -> Prop :=
 | rc_baseT : forall (t t':term),
     lcT t -> 
     lcT t' ->  (* Probably not needed, since it follows from the other two. *)
     R t t' -> rcRTT R t t'
 | rc_reflT : forall (t :term), lcT t -> rcRTT R t t.

(* Reflexive closure of R (in gmargs) *)
Inductive rcRAA (R : gmargs -> gmargs -> Prop) : gmargs -> gmargs -> Prop := 
 | rc_baseA : forall (a a':gmargs),
     lcA a -> 
     lcA a' ->  (* Probably not needed, since it follows from the other two. *)
     R a a' -> rcRAA R a a'
 | rc_reflA : forall (a :gmargs), lcA a -> rcRAA R a a.

(* Reflexive closure of R (in alist) *)
Inductive rcRLL (R : alist -> alist -> Prop) : alist -> alist -> Prop := 
 | rc_baseL : forall (l l':alist),
     lcL l ->
     lcL l' ->  (* Probably not needed, since it follows from the other two. *)
     R l l' -> rcRLL R l l'
 | rc_reflL : forall (l :alist), lcL l -> rcRLL R l l.

(* Reflexive closure of R (in cont) *)
Inductive rcRCC (R : cont -> cont -> Prop) : cont -> cont -> Prop := 
 | rc_baseC : forall (c c':cont),
     lcC c -> 
     lcC c' ->  (* Probably not needed, since it follows from the other two. *)
    R c c' -> rcRCC R c c'
 | rc_reflC : forall (c :cont), lcC c -> rcRCC R c c.




(**************************
 * Transitive closures
 **************************)

(* Transitive closure of R (in terms) *)
Inductive tcRTT (R : term -> term -> Prop) : term -> term -> Prop :=
 | tc_base : forall (t t':term),
     lcT t -> 
     lcT t' ->  (* Probably not needed, since it follows from the other two. *)
     R t t' -> tcRTT R t t'
 | tc_trans : forall (t t' t'':term),
     tcRTT R t t' -> tcRTT R t' t'' -> tcRTT R t t''.


(*......*)


(**************************
 * Reflexive-transitive closures
 **************************)


(* Reflexive-transitive closure of R (in terms) *)

Definition rtcRTT (R : term -> term -> Prop) : term -> term -> Prop := tcRTT (rcRTT R).


(*......*)



(**************************
 * Compatible closures
 **************************)
  
(* Compatible closure of R (in terms) *)

Inductive ccRTT (R : term -> term -> Prop) : term -> term -> Prop :=
 | cc_base : forall (t t':term),
     R t t' -> ccRTT R t t'  (* here we are assuming that (R t t') -> lcT t /\ lcT t', 
                               which is ok for beta but has to be proved for the other rules *)
 (* the alternative definition is
    | cc_base : forall (t t':term), lcT t ->  lcT t' ->  R t t' -> ccRTT R t t'    *)
 | cc_abs : forall (t t':term) (L:vars),
     (forall (x:var), x `notin` L ->
     ccRTT R (openT t (var_f x)) (openT t' (var_f x))) -> ccRTT R (abs t) (abs t')
 | cc_app1 : forall (t t':term) (a:gmargs), lcA a ->
     ccRTT R t t' -> ccRTT R (app t a) (app t' a)
 | cc_app2 : forall (t:term) (a a':gmargs), lcT t ->
     ccRTA R a a' -> ccRTT R (app t a) (app t a')
with ccRTA (R : term -> term -> Prop) : gmargs -> gmargs -> Prop :=    (* in gmargs *)
 | cc_args1 : forall (u u':term) (l:alist) (c:cont), lcL l -> lcC c ->
     ccRTT R u u' -> ccRTA R (args u l c) (args u' l c)
 | cc_args2 : forall (u:term) (l l':alist) (c:cont), lcT u -> lcC c ->
     ccRTL R l l' -> ccRTA R (args u l c) (args u l' c)
 | cc_args3 : forall (u:term) (l:alist) (c c':cont), lcT u -> lcL l ->
     ccRTC R c c' -> ccRTA R (args u l c) (args u l c')
with ccRTL (R : term -> term -> Prop) : alist -> alist -> Prop :=     (* in alist *)
 | cc_head : forall (u u':term) (l:alist) , lcL l ->
     ccRTT R u u' -> ccRTL R (acons u l) (acons u' l)
 | cc_tail : forall (u :term) (l l':alist) , lcT u ->
     ccRTL R l l' -> ccRTL R (acons u l) (acons u l')
with ccRTC (R : term -> term -> Prop) : cont -> cont -> Prop :=       (* in cont *)
 | cc_cabs : forall (v v':term) (L:vars),
     (forall (x:var), x `notin` L ->
     ccRTT R (openT v (var_f x))  (openT v' (var_f x)))
      -> ccRTC R (cabs v) (cabs v').


Scheme ccRTT_ind_4 := Induction for ccRTT Sort Prop
  with ccRTA_ind_4 := Induction for ccRTA Sort Prop
  with ccRTL_ind_4 := Induction for ccRTL Sort Prop   
  with ccRTC_ind_4 := Induction for ccRTC Sort Prop.


Combined Scheme ccRT_mutind from
         ccRTT_ind_4, ccRTA_ind_4, ccRTL_ind_4, ccRTC_ind_4.


(* Compatible closure of R (in gmargs) *)
Inductive ccRAT (R : gmargs -> gmargs -> Prop) : term -> term -> Prop :=     (* in terms *)
 | ccA_abs : forall (t t':term) (L:vars),
     (forall (x:var), x `notin` L ->                                     
     ccRAT R (t^x) (t'^x) )-> ccRAT R (abs t) (abs t')                          
 | ccA_app1 : forall (t t':term) (a:gmargs), lcA a ->
     ccRAT R t t' -> ccRAT R (app t a) (app t' a)
 | ccA_app2 : forall (t:term) (a a':gmargs), lcT t ->
     ccRAA R a a' -> ccRAT R (app t a) (app t a')
with ccRAA (R : gmargs -> gmargs -> Prop) : gmargs -> gmargs -> Prop :=     (* in gmargs *)
 | ccA_base : forall (a a':gmargs),
     R a a' -> ccRAA R a a'   (* here we are assuming that (R t t') -> lcT t /\ lcT t', 
                                which has to be proved for the other rules *)
 (* the alternative definition is      
 | ccA_base : forall (a a':gmargs), lcA a -> lcA a' -> R a a' -> ccRAA R a a'    *)
 | ccA_args1 : forall (u u':term) (l:alist) (c:cont), lcL l -> lcC c ->
     ccRAT R u u' -> ccRAA R (args u l c) (args u' l c)
 | ccA_args2 : forall (u:term) (l l':alist) (c:cont), lcT u -> lcC c ->
     ccRAL R l l' -> ccRAA R (args u l c) (args u l' c)
 | ccA_args3 : forall (u:term) (l:alist) (c c':cont), lcT u -> lcL l ->
     ccRAC R c c' -> ccRAA R (args u l c) (args u l c')
with ccRAL (R : gmargs -> gmargs -> Prop) : alist -> alist -> Prop :=        (* in alist *)
 | ccA_head : forall (u u':term) (l:alist), lcL l ->
     ccRAT R u u' -> ccRAL R (acons u l) (acons u' l)
 | ccA_tail : forall (u :term) (l l':alist), lcT u ->
     ccRAL R l l' -> ccRAL R (acons u l) (acons u l')
with ccRAC (R : gmargs -> gmargs -> Prop) : cont -> cont -> Prop :=          (* in cont *)
 | ccA_cabs : forall (v v':term) (L:vars),
     (forall (x:var), x `notin` L -> ccRAT R (v^x) (v'^x) )
     -> ccRAC R (cabs v) (cabs v').

Scheme ccRAT_ind_4 := Induction for ccRAT Sort Prop
  with ccRAA_ind_4 := Induction for ccRAA Sort Prop
  with ccRAL_ind_4 := Induction for ccRAL Sort Prop   
  with ccRAC_ind_4 := Induction for ccRAC Sort Prop.


Combined Scheme ccRA_mutind from
         ccRAT_ind_4, ccRAA_ind_4, ccRAL_ind_4, ccRAC_ind_4.


(* Compatible closure of RT and RA *)
Inductive ccRTRAT (RT:term->term->Prop) (RA:gmargs->gmargs->Prop) : term -> term -> Prop :=   (* in terms *)
 | ccTA_baseT : forall (t t':term),   
     RT t t' -> ccRTRAT RT RA t t'  (* here we are assuming that (RT t t') -> lcT t /\ lcT t', 
                                      which has to be proved for the other rules *)
(* the alternative definition is      
 | ccTA_baseT : forall (t t':term),
     lcT t -> lcT t' ->  RT t t' -> ccRTRAT RT RA t t' *)
 | ccTA_abs :forall (t t':term) (L:vars),
     (forall (x:var), x `notin` L -> ccRTRAT RT RA (t^x) (t'^x)) ->
     ccRTRAT RT RA (abs t) (abs t')
 | ccTA_app1 : forall (t t':term) (a:gmargs), lcA a ->
     ccRTRAT RT RA t t' -> ccRTRAT RT RA (app t a) (app t' a)
 | ccTA_app2 : forall (t:term) (a a':gmargs), lcT t ->
     ccRTRAA RT RA a a' -> ccRTRAT RT RA (app t a) (app t a')
with ccRTRAA (RT:term->term->Prop) (RA:gmargs->gmargs->Prop) : gmargs -> gmargs -> Prop :=    (* in gmargs *)
       
 | ccTA_baseA : forall (a a':gmargs),
     RA a a' -> ccRTRAA RT RA a a' (* here we are assuming that (RA a a') -> lcA a /\ lcA a', 
                                which has to be proved for the other rules *)
 (* the alternative definition is      
 | ccTA_baseA : forall (a a':gmargs), lcA a -> lcA a' -> RA a a' -> ccRTRAA RT RA a a'   *)
 | ccTA_args1 : forall (u u':term) (l:alist) (c:cont), lcL l -> lcC c ->
     ccRTRAT RT RA u u' -> ccRTRAA RT RA (args u l c) (args u' l c)
 | ccTA_args2 : forall (u:term) (l l':alist) (c:cont), lcT u -> lcC c ->
     ccRTRAL RT RA l l' -> ccRTRAA RT RA (args u l c) (args u l' c)
 | ccTA_args3 : forall (u:term) (l:alist) (c c':cont), lcT u -> lcL l ->
     ccRTRAC RT RA c c' -> ccRTRAA RT RA (args u l c) (args u l c')
with ccRTRAL (RT:term->term->Prop) (RA:gmargs->gmargs->Prop) : alist -> alist -> Prop :=     (* in alist *)
 | ccTA_head : forall (u u':term) (l:alist), lcL l ->
     ccRTRAT RT RA u u' -> ccRTRAL RT RA (acons u l) (acons u' l)
 | ccTA_tail : forall (u :term) (l l':alist), lcT u ->
     ccRTRAL RT RA l l' -> ccRTRAL RT RA (acons u l) (acons u l')
with ccRTRAC (RT:term->term->Prop) (RA:gmargs->gmargs->Prop) : cont -> cont -> Prop :=        (* in cont *)
 | ccTA_cabs : forall (v v':term) (L:vars),
     (forall (x:var), x `notin` L -> ccRTRAT RT RA (v^x) (v'^x)) ->
     ccRTRAC RT RA (cabs v) (cabs v').


Scheme ccRTRAT_ind_4 := Induction for ccRTRAT Sort Prop
  with ccRTRAA_ind_4 := Induction for ccRTRAA Sort Prop
  with ccRTRAL_ind_4 := Induction for ccRTRAL Sort Prop   
  with ccRTRAC_ind_4 := Induction for ccRTRAC Sort Prop.


Combined Scheme ccRTRA_mutind from
         ccRTRAT_ind_4, ccRTRAA_ind_4, ccRTRAL_ind_4, ccRTRAC_ind_4.



Definition ccBeta1 t t' := ccRTT beta1T t t'.
Definition ccBeta2 t t' := ccRTT beta2T t t'.
Definition ccBeta t t' := ccRTT betaT t t'.
Definition ccPi t t' := ccRTT piT t t'.
Definition ccBetaPi t t' := ccRTT betapiT t t'.
Definition ccMu t t' := ccRAT muA t t'.
Definition ccBetaPiMu t t' := ccRTRAT betapiT muA t t'.


Hint Constructors beta1T beta2T betaT piT betapiT muA.
Hint Constructors ccRTT ccRTA ccRTL ccRTC.
Hint Constructors ccRAT ccRAA ccRAL ccRAC.
Hint Constructors ccRTRAT ccRTRAA ccRTRAL ccRTRAC.


(*************************************************************************)
(** Associativity of append                                              *)
(*************************************************************************)

Definition pi_refcompCT := rcRTT (ccRTT piT).
Definition pi_refcompCA := rcRAA (ccRTA piT).
Definition pi_refcompCC := rcRCC (ccRTC piT).


Definition ccT_rc_pi := ccRTT (rcRTT piT).
Definition ccA_rc_pi := ccRTA (rcRTT piT).
Definition ccC_rc_pi := ccRTC (rcRTT piT).


Definition refccT_rc_pi := rcRTT (ccRTT (rcRTT piT)).
Definition refccA_rc_pi := rcRAA (ccRTA (rcRTT piT)).
Definition refccC_rc_pi := rcRCC (ccRTC (rcRTT piT)).



Lemma lcA_appA : forall a a', lcA a -> lcA a' -> lcA (app_args_args a a').
Proof.
  intros a a' H H0. destruct a. simpl. inversion_clear H. constructor; try assumption.
Admitted.

Lemma lcC_appCA : forall c a, lcC c -> lcA a -> lcC (app_cont_args c a).
Proof.
  intros c a H H0.
Admitted.

Lemma lc_appAA_appCA :
  (forall t:term, True) /\
  (forall a a', lcA a -> lcA a' -> lcA (app_args_args a a')) /\
  (forall l:alist, True) /\
  (forall c a, lcC c -> lcA a -> lcC (app_cont_args c a)).
Proof.
  apply (term_gmargs_alist_cont_mutind
  (fun t:term => True)
  (fun a => forall a', lcA a -> lcA a' -> lcA (app_args_args a a')) 
  (fun l:alist => True) 
  (fun c => forall a, lcC c -> lcA a -> lcC (app_cont_args c a))); try trivial.
  - (* gmargs *)
    intros u H l H0 c H1 a' H2 H3. inversion_clear H2. simpl. constructor; try assumption.
    apply H1; assumption.
  - (* cont *)    
    intros v H a H0 H1. simpl. inversion_clear H0. constructor. intros x. destruct v eqn:vvv.
    + cbn. destruct (lt_eq_lt_dec n 0) eqn:test.
      * inversion s.
        -- simpl.
Admitted.

Lemma lcT_appT : forall t a a', lcT t -> lcA a -> lcA a' -> lcT (app t (app_args_args a a')).
Admitted.

Lemma lcA_appAA_appA : forall a a' a'', lcA a ->  lcA a' -> lcA a'' ->
                                  lcA (app_args_args (app_args_args a a') a'').
Admitted.

Lemma lcA_appA_appAA : forall a a' a'', lcA a ->  lcA a' -> lcA a'' ->
                                  lcA (app_args_args a (app_args_args a' a'')).
Admitted.

Lemma lcA_appC_appC : forall u l c a' a'', lcT u -> lcL l -> lcC c ->  lcA a' -> lcA a'' ->
                                      lcA (args u l (app_cont_args (app_cont_args c a') a'')).
Admitted.

Lemma lcC_appTx_appTx : forall v a a', lcT v  ->  lcA a -> lcA a' ->
                                    lcC (cabs (app_term_x_args (app_term_x_args v a) a')).
Admitted.

Lemma open_app : forall u t a, openT (app t a) u = app (openT t u) (openA a u).
Proof. reflexivity. Qed.

Lemma open_args : forall u t l c, openA (args t l c) u = args (openT t u) (openL l u) (openC c u).
Proof. reflexivity. Qed.


Lemma lc_open : forall u, lcT u ->
                     (forall t, lcT t -> lcT (openT t u)) /\
                     (forall a, lcA a -> lcA (openA a u)) /\
                     (forall l, lcL l -> lcL (openL l u)) /\
                     (forall c, lcC c -> lcC (openC c u)) .
Admitted. (*---AQUI---*)


Lemma  lcT_lcA_openA : forall t a, lcT t -> lcA a -> lcA (openA a t).
Proof.
  intros t a H H0.  apply lc_open in H. destruct H. destruct H1. apply H1. assumption.
Qed.

Lemma pi_lc : forall e1 e2, piT e1 e2 -> lcT e1.
Proof.
  intros e1 e2 H. inversion H; auto.
Qed.


Ltac lc_tac :=
   match goal with
   | [ |- lcT (app _ (app_args_args _ _ )) ] => apply lcT_appT; assumption
   
   | [ |- lcT (app _ (app_args_args (app_args_args _ _ ) _ ))] => constructor; [assumption | apply lcA_appAA_appA ; assumption ]

   | [ |- lcT (app _ (app_args_args _ (app_args_args _ _))) ] => constructor; [assumption | apply lcA_appA_appAA ; assumption ]

   | [ |- lcT (app (app _ _) _) ] => constructor; [constructor;assumption | assumption]
   end.

(*---------------------------------------------------------------------*)
(*
Lemma append_assoc : (forall t a a', lcT t -> lcA a -> lcA a' ->
                         (refccT_rc_pi (app_term_args (app_term_args t a) a')
                                       (app_term_args t (app_args_args a a'))) /\ 
                         (refccT_rc_pi (app_term_x_args (app_term_x_args t a) a')
                                       (app_term_x_args t (app_args_args a a'))) ) /\
                     (forall a a' a'', lcA a -> lcA a' -> lcA a'' ->
                                  refccA_rc_pi (app_args_args (app_args_args a a') a'')
                                               (app_args_args a (app_args_args a' a''))) /\
                     (forall l:alist, True) /\
                     (forall c a a', lcC c -> lcA a -> lcA a' ->
                                refccC_rc_pi (app_cont_args (app_cont_args c a) a')
                                             (app_cont_args c (app_args_args a a'))).
Proof.
  apply (term_gmargs_alist_cont_mutind 
           (fun t => forall a a', lcT t -> lcA a -> lcA a' ->
                          (refccT_rc_pi (app_term_args (app_term_args t a) a') 
                                        (app_term_args t (app_args_args a a'))) /\
                          (refccT_rc_pi (app_term_x_args (app_term_x_args t a) a')
                                        (app_term_x_args t (app_args_args a a'))) )
           (fun a => forall a' a'', lcA a -> lcA a' -> lcA a'' ->
                            refccA_rc_pi (app_args_args (app_args_args a a') a'')
                                         (app_args_args a (app_args_args a' a'')))
           (fun l => True)
           (fun c => forall a a', lcC c -> lcA a -> lcA a' ->
                          refccC_rc_pi (app_cont_args (app_cont_args c a) a')
                                       (app_cont_args c (app_args_args a a'))) ).
  - (* var_b *)
    intros n a a' H H0 H1. inversion H.
  - (* var_f *)
    intros x a a' H H0 H1; split.
    + simpl. unfold refccT_rc_pi. apply rc_reflT. apply lcT_appT; assumption.
    + simpl. unfold refccT_rc_pi. apply rc_baseT; try lc_tac.
      * apply cc_base; try lc_tac. apply rc_baseT; try lc_tac. constructor; assumption.
  - (* abs *)
    intros t H a a' H0 H1 H2. split.
    + simpl. unfold refccT_rc_pi. apply rc_reflT.lc_tac.  
    + simpl. unfold refccT_rc_pi. constructor; try lc_tac. apply cc_base; try lc_tac.
      apply rc_baseT; try lc_tac. constructor; assumption.
  - (* app *)
    intros t H a H0 a0 a' H1 H2 H3.
    assert (Haux: (forall a a' : gmargs, lcT t -> lcA a -> lcA a' ->
      refccT_rc_pi (app_term_args (app_term_args t a) a') (app_term_args t (app_args_args a a')) /\
      refccT_rc_pi (app_term_x_args (app_term_x_args t a) a')
                   (app_term_x_args t (app_args_args a a'))) ->
                (forall a a' : gmargs, lcT t -> lcA a -> lcA a' ->
                                  refccT_rc_pi (app_term_args (app_term_args t a) a')
                                               (app_term_args t (app_args_args a a'))) /\
                (forall a a' : gmargs, lcT t -> lcA a -> lcA a' ->
                                  refccT_rc_pi (app_term_x_args (app_term_x_args t a) a')
                                               (app_term_x_args t (app_args_args a a'))) ).
    { intros H4; split;  intros a1 a'0 H5 H6 H7; apply H4; assumption. }
    apply Haux in H. destruct H. clear Haux. split.
    + simpl. inversion_clear H1. apply rc_baseT; try lc_tac. apply cc_app2.
      specialize (H0 a0 a' H6 H2 H3).

*)
      

  
(*---------------------------------------------------------------------*)

(*
Lemma append_assoc : (forall t a a', lcT t -> lcA a -> lcA a' ->
                         (ccT_rc_pi (app_term_args (app_term_args t a) a')
                                       (app_term_args t (app_args_args a a'))) /\ 
                         (ccT_rc_pi (app_term_x_args (app_term_x_args t a) a')
                                       (app_term_x_args t (app_args_args a a'))) ) /\
                     (forall a a' a'', lcA a -> lcA a' -> lcA a'' ->
                                  ccA_rc_pi (app_args_args (app_args_args a a') a'')
                                               (app_args_args a (app_args_args a' a''))) /\
                     (forall l:alist, True) /\
                     (forall c a a', lcC c -> lcA a -> lcA a' ->
                                ccC_rc_pi (app_cont_args (app_cont_args c a) a')
                                             (app_cont_args c (app_args_args a a'))).
Proof.
  apply (term_gmargs_alist_cont_mutind 
           (fun t => forall a a', lcT t -> lcA a -> lcA a' ->
                          (ccT_rc_pi (app_term_args (app_term_args t a) a') 
                                        (app_term_args t (app_args_args a a'))) /\
                          (ccT_rc_pi (app_term_x_args (app_term_x_args t a) a')
                                        (app_term_x_args t (app_args_args a a'))) )
           (fun a => forall a' a'', lcA a -> lcA a' -> lcA a'' ->
                            ccA_rc_pi (app_args_args (app_args_args a a') a'')
                                         (app_args_args a (app_args_args a' a'')))
           (fun l => True)
           (fun c => forall a a', lcC c -> lcA a -> lcA a' ->
                          ccC_rc_pi (app_cont_args (app_cont_args c a) a')
                                       (app_cont_args c (app_args_args a a'))) ).
  - (* var_b *)
    intros n a a' H H0 H1. inversion H.
  - (* var_f *)
    intros x a a' H H0 H1; split.
    + simpl. unfold ccT_rc_pi. apply cc_base; try lc_tac. apply rc_reflT; lc_tac.
    + simpl. unfold ccT_rc_pi. apply cc_base; try lc_tac. constructor; try lc_tac.
      constructor; assumption.
  - (* abs *)
    intros t H a a' H0 H1 H2. split.
    + simpl. apply cc_base; try lc_tac. apply rc_reflT; lc_tac.
    + simpl. unfold ccT_rc_pi. apply cc_base; try lc_tac. apply rc_baseT; try lc_tac.
      constructor; assumption.
  - (* app *)
    intros t H a H0 a0 a' H1 H2 H3.
    assert (Haux: (forall a a' : gmargs, lcT t -> lcA a -> lcA a' ->
      ccT_rc_pi (app_term_args (app_term_args t a) a') (app_term_args t (app_args_args a a')) /\
      ccT_rc_pi (app_term_x_args (app_term_x_args t a) a')
                   (app_term_x_args t (app_args_args a a'))) ->
                (forall a a' : gmargs, lcT t -> lcA a -> lcA a' ->
                                  ccT_rc_pi (app_term_args (app_term_args t a) a')
                                               (app_term_args t (app_args_args a a'))) /\
                (forall a a' : gmargs, lcT t -> lcA a -> lcA a' ->
                                  ccT_rc_pi (app_term_x_args (app_term_x_args t a) a')
                                               (app_term_x_args t (app_args_args a a'))) ).
    { intros H4; split;  intros a1 a'0 H5 H6 H7; apply H4; assumption. }
    apply Haux in H. destruct H. clear Haux. split.
    + simpl. inversion_clear H1. unfold ccT_rc_pi. apply cc_app2. apply H0; assumption.
    + inversion_clear H1. simpl. destruct t eqn:ttt.
      * inversion H5. 
      * simpl.

*)

(* ------------------------------------------------- *)

Lemma append_assoc : (forall t a a', lcT t -> lcA a -> lcA a' ->
                         (pi_refcompCT (app_term_args (app_term_args t a) a')
                                       (app_term_args t (app_args_args a a'))) /\ 
                         (pi_refcompCT (app_term_x_args (app_term_x_args t a) a')
                                       (app_term_x_args t (app_args_args a a'))) ) /\
                     (forall a a' a'', lcA a -> lcA a' -> lcA a'' ->
                                  pi_refcompCA (app_args_args (app_args_args a a') a'')
                                               (app_args_args a (app_args_args a' a''))) /\
                     (forall l:alist, True) /\
                     (forall c a a', lcC c -> lcA a -> lcA a' ->
                                pi_refcompCC (app_cont_args (app_cont_args c a) a')
                                             (app_cont_args c (app_args_args a a'))).
Proof.
  apply (term_gmargs_alist_cont_mutind 
           (fun t => forall a a', lcT t -> lcA a -> lcA a' ->
                          (pi_refcompCT (app_term_args (app_term_args t a) a') 
                                        (app_term_args t (app_args_args a a'))) /\
                          (pi_refcompCT (app_term_x_args (app_term_x_args t a) a')
                                        (app_term_x_args t (app_args_args a a'))) )
           (fun a => forall a' a'', lcA a -> lcA a' -> lcA a'' ->
                            pi_refcompCA (app_args_args (app_args_args a a') a'')
                                         (app_args_args a (app_args_args a' a'')))
           (fun l => True)
           (fun c => forall a a', lcC c -> lcA a -> lcA a' ->
                          pi_refcompCC (app_cont_args (app_cont_args c a) a')
                                       (app_cont_args c (app_args_args a a'))) ).
  - (* var_b *)
    intros n a a' H H0 H1. inversion H.
  - (* var_f *)
    intros x a a' H H0 H1; split.
    + simpl. unfold pi_refcompCT. apply rc_reflT. lc_tac. 
    + simpl. unfold pi_refcompCT. constructor; try lc_tac.
      * constructor; try lc_tac. constructor; assumption.
  - (* abs *)
    intros t H a a' H0 H1 H2. split.
    + simpl. apply rc_reflT. lc_tac.
    + simpl. unfold pi_refcompCT. constructor; try lc_tac. 
      * apply cc_base; try lc_tac. constructor; assumption.
  - (* app *)
    intros t H a H0 a0 a' H1 H2 H3.
    assert (Haux: (forall a a' : gmargs, lcT t -> lcA a -> lcA a' ->
      pi_refcompCT (app_term_args (app_term_args t a) a') (app_term_args t (app_args_args a a')) /\
      pi_refcompCT (app_term_x_args (app_term_x_args t a) a')
                   (app_term_x_args t (app_args_args a a'))) ->
                (forall a a' : gmargs, lcT t -> lcA a -> lcA a' ->
                                  pi_refcompCT (app_term_args (app_term_args t a) a')
                                               (app_term_args t (app_args_args a a'))) /\
                (forall a a' : gmargs, lcT t -> lcA a -> lcA a' ->
                                  pi_refcompCT (app_term_x_args (app_term_x_args t a) a')
                                               (app_term_x_args t (app_args_args a a'))) ).
    { intros H4; split;  intros a1 a'0 H5 H6 H7; apply H4; assumption. }
    apply Haux in H. destruct H. clear Haux. split.
 (*   + simpl. inversion_clear H1. unfold pi_refcompCT. constructor; try lc_tac.
      apply cc_app2. unfold pi_refcompCA in H0. apply (H0 a0 a' H6 H2) in H3. 
      inversion_clear H3.
      * assumption.
      * 
*)
    (*----- alternativa -----*)
    (*
    + simpl. unfold pi_refcompCT. constructor.
      * inversion_clear H1. lc_tac.
      * inversion_clear H1. lc_tac.
      * inversion_clear H1. apply cc_app2. admit.
    + simpl. destruct t eqn:ttt.
      * destruct n eqn:nnn; inversion H1.
        -- destruct (testINargs_rec 0 a); inversion H6. admit. admit.
        -- inversion H6. admit.
      * simpl. inversion_clear H1. unfold pi_refcompCT. apply rc_baseT. constructor.
        -- constructor; [constructor;assumption | assumption].
        -- assumption.
        -- constructor; [constructor;assumption | apply lcA_appA; assumption].
        -- apply cc_base.
           ++ constructor. constructor; [constructor;assumption | assumption]. assumption.
           ++ constructor; [constructor; assumption | apply lcA_appA; assumption].
           ++ constructor; [constructor; assumption | assumption | assumption].
      * simpl. unfold pi_refcompCT. inversion_clear H1. apply rc_baseT.
        -- admit.
        -- admit.
        -- apply cc_base.
           ++ admit.
           ++ admit.
           ++ constructor; [constructor; assumption | assumption | assumption].
      * simpl. unfold pi_refcompCT. inversion_clear H1. apply rc_baseT.
          (* tem que se usar a indução !!! *)
           admit. admit. admit.
  - (* args *)
    intros u H l H0 c H1 a' a'' H2 H3 H4. simpl. inversion_clear H2. constructor.
    + apply lcA_appC_appC; assumption. 
    + apply cc_args3. unfold pi_refcompCC in H1. destruct (H1 a' a''); try assumption. admit.
  - (* anil *) trivial.
  - (* acons *) trivial. 
  - (* cabs *)
    intros v H a a' H0 H1 H2. simpl. constructor.
    + inversion H0. destruct v.
      * simpl. destruct n.
        -- destruct (testINargs_rec 0 a) eqn:zzz.
           ++ constructor. intro x. rewrite -> open_app. constructor.
              ** rewrite -> open_app. cbn. constructor.
                 --- constructor. 
                 --- apply lcT_lcA_openA; [constructor|assumption].         
                ** apply lcT_lcA_openA; [constructor|assumption]. 
           ++ constructor. intro x. rewrite -> open_app. constructor.
              ** cbn. constructor. 
              **  apply lcT_lcA_openA.
                  --- constructor.
                  --- apply lcA_appA; assumption.
        -- constructor. intro x. rewrite -> open_app. constructor.
           ++ rewrite -> open_app. constructor.
              ** apply H4.
              ** apply lcT_lcA_openA; [constructor|assumption].
           ++ apply lcT_lcA_openA; [constructor|assumption].
      * simpl. constructor. intro x0. rewrite -> open_app. constructor.
        -- rewrite -> open_app. constructor.
           ++ cbn. constructor.  
           ++ apply lcT_lcA_openA; [constructor|assumption].
        -- apply lcT_lcA_openA; [constructor|assumption].
      * simpl. constructor. intro x. rewrite -> open_app. constructor.
        -- rewrite -> open_app. constructor. apply H4.
           apply lcT_lcA_openA; [constructor|assumption].
        -- apply lcT_lcA_openA; [constructor|assumption].
      * admit. (* apply pi_lc. *)
    + constructor. admit. (* apply H. *)

*)
Admitted.

      

Definition ccBeta1T := ccRTT beta1T.
