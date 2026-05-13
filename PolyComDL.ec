(* Constant-Size Commitments to Polynomials and Their Applications - PolyComDl *)

require import AllCore PolyCom Bilinear List IntDiv Ring Bigalg AddList AddPoly Distr DList DProd AddDistr.
require import FelTactic.


clone Bilinear.Bl as Bl.

clone AddPoly as PolyHelp.

import PolyHelp.
import BasePoly.
import Bl.ZP.ZModE.











clone export PolynomialCommitment as PolyComDL with
  type ck <- Bl.GB.group list,
  type witness <- Bl.GB.group,
  type commitment <- Bl.GB.group, 
  type openingkey <- unit,
  type coeff <- exp,
  op t <- Bl.t,
  axiom t_valid <- Bl.t_valid,
  theory IDCoeff <- R,
  theory BasePoly <- BasePoly,
  op coeff_sample = Bl.FD.dt.


abbrev ( ^ ) = Bl.ZP.( ^ ).


(*fixed*)
lemma prod_sum_eq (a : exp) m :
    foldr Bl.GB.( * ) Bl.GB.e
      (mkseq (fun (i : int) => Bl.GB.g ^ (nth a m i)) (size m)) =
    Bl.GB.g ^ foldr Bl.ZP.ZModE.(+) Bl.ZP.ZModE.zero m.
proof.
  elim: m => [|x l ih].
  + rewrite mkseq0 /=.
    smt(Bl.pow_add @Bl.GB @Bl.ZP.ZModE.ZModpField).
  + simplify.
    have h' : Bl.GB.g ^ (x + foldr Bl.ZP.ZModE.(+) Bl.ZP.ZModE.zero l) =
              Bl.GB.( * ) (Bl.GB.g ^ x)
                          (Bl.GB.g ^ foldr Bl.ZP.ZModE.(+) Bl.ZP.ZModE.zero l).
    + by rewrite Bl.pow_add.
    rewrite h'. rewrite -ih.
    rewrite mkseq_add. smt(). smt(@List).
    rewrite List.foldr_cat. rewrite mkseq1. simplify.
    have h'' : forall (b c d : Bl.GB.group),
        c = d => Bl.GB.( * ) b c = Bl.GB.( * ) b d by smt().
    apply h''.
    apply eq_foldr; trivial.
    apply (eq_from_nth Bl.GB.g). smt(@List). move => i hi.
    rewrite size_mkseq in hi. rewrite nth_mkseq. smt(). rewrite nth_mkseq. smt().
    simplify. smt(@List).
qed. 








  (* Define the key algortihms and related lemmas *)  
  op prodEx = fun x m  => List.foldr Bl.GB.( * ) Bl.GB.e
      (mkseq (fun (i : int) => ( ^ )(nth Bl.GB.g x i)
          (m.[i])) (size x + 1)).

  (* We first want to prove we can rephrase the combination of mkKey and prodEx in
            a way more favorable to induction *)

     
(*fixed*)
lemma mkKey_ga a : nth Bl.GB.g (Bl.mkKey a) 1 = Bl.GB.g ^ a.
proof.
  rewrite /Bl.mkKey nth_mkseq.
  + by smt(Bl.t_valid).
  simplify.
smt(@Bl.ZP.ZModE).

qed.









(*fixed*)
lemma prodExSimp a m :
    size m <= Bl.t =>
    prodEx (Bl.mkKey a) (polyL m) =
    List.foldr Bl.GB.( * ) Bl.GB.e
      (mkseq (fun i => (nth Bl.GB.e (Bl.mkKey a) i) ^ (polyL m).[i]) (size m)).
proof.
  move => h. rewrite /prodEx /Bl.mkKey.
  apply foldr_eq_partR.
  + smt(@Bl.GB).
  + smt(@Bl.GB).
  + smt(@Bl.GB).
  + smt(@Bl.GB).
  + rewrite !size_mkseq. smt(Bl.t_valid).
  + rewrite !size_mkseq.
    rewrite take_mkseq; first by smt(Bl.t_valid).
    have hmax : max 0 (size m) = size m by smt(@List).
    rewrite hmax.
    apply eq_in_mkseq => i hi /=.
    have : nth Bl.GB.g
             (mkseq (fun (j : int) => Bl.GB.g ^ exp a j) (Bl.t + 1)) i =
           nth Bl.GB.e
             (mkseq (fun (j : int) => Bl.GB.g ^ exp a j) (Bl.t + 1)) i
      by smt(nth_mkseq @List Bl.t_valid).
    by move => ->.
  + rewrite !size_mkseq.
    apply (all_nth _ Bl.GB.g).
    move => i hi /=.
    rewrite nth_drop; first 2 by smt(@List).
    rewrite nth_mkseq.
    + split; first by smt(@List).
      rewrite size_drop in hi. smt(@List).
      rewrite size_mkseq in hi. move => _. smt(Bl.t_valid).
    simplify.
    have hzero : (polyL m).[max 0 (size m) + i] = Bl.ZP.ZModE.zero.
    + apply gedeg_coeff.
      have hd : deg (polyL m) <= size m by apply degL_le.
      smt(@List).
    rewrite hzero.

    smt(Bl.pow_add @Bl.GB @Bl.ZP.ZModE.ZModpField).

qed.










lemma peval_simp_opt (m :poly) a :

    peval m a = foldr ( +) zero

      (mkseq (fun i => ( * )  m.[i] (exp a i))

        (deg m)).

proof.

  rewrite -foldr_mkseq_bigi_eq. smt(ge0_deg). move => @/peval. trivial. rewrite BigCf.BCA.big_int_recr. smt(@BasePoly).

  simplify. rewrite gedeg_coeff. trivial. smt(@R). 

qed.



lemma peval_simp_gen (m :poly) a j : deg m <= j  =>

    peval m a = foldr ( + ) zero

    (mkseq (fun i => ( * )  m.[i] (exp a i)) j).

proof.

    rewrite peval_simp_opt. move => h. apply foldr_eq_partL; trivial. smt(@R). smt(@R). smt(@R). smt(@List).

    (* first part equal *) smt(@List).

    (* zero_tail *) apply (all_nth _ zero). move => i hi. simplify. rewrite nth_drop. smt(@List). smt().  

    rewrite nth_mkseq. smt(@List). simplify. rewrite gedeg_coeff. smt(@List). smt(@R).

qed.



(* It's convient to keep the org form for induction *)

lemma peval_simp (m :poly) a :

    peval m a = foldr ( +) zero

      (mkseq (fun i => ( * )  m.[i] (exp a i))

        (deg m + 1)).

proof.

  apply peval_simp_gen. smt().

qed.








      
lemma comPolEvalSub (a : exp) m :
    foldr Bl.GB.( * ) Bl.GB.e (mkseq (fun (i : int) =>
        (Bl.GB.g ^ (exp a i)) ^ (polyL m).[i])
     (size m)) =
    Bl.GB.g ^ peval (polyL m) a.
proof.
  
 
    rewrite (peval_simp_gen _ _ (size m)). smt(@Poly degL_le).  rewrite -(prod_sum_eq Bl.ZP.ZModE.zero _). rewrite size_mkseq.
    apply foldr_eq_partR. smt(@Bl.GB). smt(@Bl.GB). smt(@Bl.GB). smt(@Bl.GB). rewrite !size_mkseq. smt(degL_le).
    (* Show the first bit is equal *)
    rewrite size_mkseq. apply (eq_from_nth Bl.GB.g). rewrite !size_mkseq. rewrite size_take.
    smt(@Poly). rewrite size_mkseq. smt(degL_le). move => i h. rewrite nth_mkseq. rewrite size_mkseq in h. smt(@Poly).
    rewrite nth_take. smt(@Poly @List). smt(@Poly @List). rewrite nth_mkseq. rewrite size_mkseq in h.
    smt(degL_le). simplify. rewrite nth_mkseq. rewrite size_mkseq in h.
    smt(@Poly). simplify.
    rewrite -Bl.ZP.expM. smt(@Bl.ZP). 
    (* Show the trail is nothing *)
    rewrite size_mkseq. rewrite (all_nth _ Bl.GB.e). move => i h. simplify. rewrite nth_drop.
    smt(). smt(). rewrite nth_mkseq. rewrite size_drop in h. smt(@List).    rewrite size_mkseq in h.  smt(@Poly). simplify.
    have : forall a b, b = zero => a^b = Bl.GB.e. smt(@Bl.ZP). move => h''.  apply h''.
    apply gedeg_coeff. smt(degL_le).
qed.

lemma comPolEval a m : deg m <= Bl.t =>
    prodEx (Bl.mkKey a) m = Bl.GB.g ^ (peval m a).
proof.
 move => h. case : (surj_polyL m Bl.t h). move => s h'. elim h'; move => h' h'' @/Bl.mkKey.
  rewrite h''. rewrite prodExSimp. smt(). move => @/Bl.mkKey.
  rewrite -comPolEvalSub. congr. apply (eq_from_nth Bl.GB.g). smt(@List). move => i hi.
  rewrite !nth_mkseq. smt(@List). smt(@List). simplify. rewrite nth_mkseq. smt(@List). 
  simplify. trivial. 
qed.

  (* Now we are ready to define the main commitment scheme *) 

 (* PK = g, g^α, . . . , g^α^t *)(*fixed*)
 module PolyComDLScheme : PC_Scheme = {
  proc setup() : Bl.GB.group list = {
    var a : Bl.ZP.exp;
    var pk : Bl.GB.group list;

    a <$ Bl.FD.dt;
    pk <- Bl.mkKey a;
    
    return pk;
  }
  
  (* c = Prod_(j=0)^t x_j^(phi_j) *)
  proc commit(x: Bl.GB.group list, m: poly) : Bl.GB.group * unit = {
    return (prodEx x m, tt);
  }
  
  (* Checks the provided polynomials matches and returns it else zero polynomial *)
  proc open(x: Bl.GB.group list, c: Bl.GB.group, m: poly, d: unit) : poly = {
    var c';

    c' <- prodEx x m;
    return (if (c = c') then m else poly0);
  }
  
  (* Checks polynomial matches commit *)
  proc verifypoly(x: Bl.GB.group list, c: Bl.GB.group, m: poly, d: unit) : bool = {
    var c';
    c' <- prodEx x m;
    return (c = c' /\ deg m <= Bl.t);
  }

  (* Sample the polynomial at the point and create the witness *)
  proc createwitness(x: Bl.GB.group list, m: poly, i: Bl.ZP.exp, d: unit) :
      Bl.ZP.exp * Bl.GB.group = {
    var w;
    var phi : Bl.ZP.exp;
    var psi;
    
    phi <- peval m i;
    
    (* φ(x)−φ(i) / (x−i), this is supposed to be quotient of φ(x) divided by (x-i) *)
    psi <- (edivpoly (m - polyC phi) (X - polyC i)).`1;
    
    (* wi = g^ψi(α) *)
    w <- prodEx x psi;
    
    return (phi, w);
  }

  
  proc verifyeval(x: Bl.GB.group list, c: Bl.GB.group, i: Bl.ZP.exp, phii: Bl.ZP.exp, w: Bl.GB.group) : bool = {
  var r, r';
  r  <- Bl.e w (Bl.GB.( / ) (nth Bl.GB.g x 1) (Bl.GB.g ^ i));
  r' <- Bl.ZP_GT.( ^ ) Bl.GT.g phii;
  return Bl.e c Bl.GB.g = Bl.GT.( * ) r r';
  }

}.






(*fixed*)
lemma PolyComDLScheme_Correctness :
  hoare[Correctness(PolyComDLScheme).main : true ==> res].
proof.
  proc. inline *. wp. rnd. auto. progress.
  case (Bl.t{hr} < (deg p{hr})). smt(). move => h. simplify.
  split. smt().
  rewrite comPolEval. smt().
  rewrite comPolEval.
  apply (degDiv2 _ _ Bl.t{hr}).
  have hpc : deg (polyC (peval p{hr} i{hr})) <= 1.
  + case (peval p{hr} i{hr} = Bl.ZP.ZModE.zero) => hpz; smt(@BasePoly).
  have hsub : deg (p{hr} - polyC (peval p{hr} i{hr}))
              <= max (deg p{hr}) (deg (polyC (peval p{hr} i{hr}))).
  + smt(@BasePoly).
  smt(Bl.t_valid).
  simplify.
  rewrite Bl.e_pow1. rewrite Bl.e_g_g. rewrite mkKey_ga.
  rewrite -Bl.ZP.expB.
  rewrite Bl.e_pow1. rewrite Bl.e_pow2. rewrite Bl.e_g_g.
  rewrite -Bl.ZP_GT.expM.
  rewrite -Bl.ZP_GT.expD.
  rewrite -Bl.ZP_GT.pow_bij.

have hrem : (edivpoly (p{hr} - polyC (peval p{hr} i{hr})) (X - polyC i{hr})).`2 = poly0.
  + have h1 := polyRemThem_r (p{hr} - polyC (peval p{hr} i{hr})) i{hr}.
    have h2 : peval (p{hr} - polyC (peval p{hr} i{hr})) i{hr} = zero.
    + smt(peval_add peval_neg peval_polyC @R).
    smt(@BasePoly).

have hdiv : p{hr} - polyC (peval p{hr} i{hr}) =
    (edivpoly (p{hr} - polyC (peval p{hr} i{hr})) (X - polyC i{hr})).`1 * (X - polyC i{hr}).
  + have := polyRemThem_corr (p{hr} - polyC (peval p{hr} i{hr})) (X - polyC i{hr}) (Xi_neq_0 i{hr}).
    smt(@BasePoly).


have heval : peval (p{hr} - polyC (peval p{hr} i{hr})) a =
    peval (edivpoly (p{hr} - polyC (peval p{hr} i{hr})) (X - polyC i{hr})).`1 a *
    peval (X - polyC i{hr}) a.
  + have hxi := peval_over_Xi
      (edivpoly (p{hr} - polyC (peval p{hr} i{hr})) (X - polyC i{hr})).`1 i{hr} a.
    smt(@BasePoly).

smt(peval_add peval_neg peval_polyC peval_X @R).

qed.



















   lemma not_inv (x : exp) : one - x <> - x.
       have : forall (a b c : exp), a <> c + b => a - b <> c.
       smt(@Bl.ZP.ZModE). move => h. apply h. smt(@Bl.ZP.ZModE).
     qed.


       
  module Adv (Adv : AdvPB) : Bl.TsdhAdv = {
    proc comp(h : Bl.GB.group list) : exp * Bl.GB.group  = {
      var c, phi, phi', d, d';
      (c, phi, phi', d, d') <@ Adv.forge(h);
      return (one - factorFind (phi - phi') h, Bl.GB.g);
    }
  }.


lemma PolyComDLScheme_PolynomialBinding (A <: AdvPB) &m :
      Pr[PolynomialBinding(PolyComDLScheme, A).main() @ &m : res] <=
      Pr[Bl.Tsdh(Adv(A)).main() @ &m : res].
proof.
  byequiv. proc. inline *. auto. call (_ : true). auto. progress.
  (* main - not inverse *)
  rewrite H1 in H3.
  have h : peval result_R.`2 aL = peval result_R.`3 aL.
  + apply (Bl.GB_pow_bij Bl.GB.g); first by apply Bl.g_neq_e.
    by rewrite -!comPolEval.
  rewrite factorFindCorr; [trivial | trivial | apply not_inv].
  rewrite H1 in H3. rewrite factorFindCorr; first trivial.
  have h' : peval result_R.`2 aL = peval result_R.`3 aL.
  + apply (Bl.GB_pow_bij Bl.GB.g); first by apply Bl.g_neq_e.
    by rewrite -!comPolEval.
  have g : aL + (one - aL) = one by smt(@Bl.ZP.ZModE.ZModpField).
  smt().
 smt(@Bl.GB @Bl.ZP.ZModE).
  smt(). smt().
qed.

  


  
 
    (* EvaluationBinding *)
module Adv2 (Adv : AdvEB) : Bl.TsdhAdv = {
  proc comp(ga : Bl.GB.group list) : exp * Bl.GB.group = {
      var c, w, w' : Bl.GB.group;
      var phi, phi', i : exp;
      (c, i, phi, w, phi', w') <@ Adv.forge(ga);
        return (if (Bl.GB.g^ i = nth Bl.GB.g ga 1) then
        (one - i, Bl.GB.g)
        else
        (-i,(Bl.GB.(/)w w')^(one/(phi' -phi))));
    }
  }. 


(*fixed*)
lemma PolyComDLScheme_EvaluationBinding (A <: AdvEB) &m :
    Pr[EvaluationBinding(PolyComDLScheme, A).main() @ &m : res] <=
    Pr[Bl.Tsdh(Adv2(A)).main() @ &m : res].
    proof.
      
    
  byequiv. proc. inline*. auto. call(:true). auto. progress. 
 (* Goal one *)
  + case (result_R.`2 = aL); move => h. 
  (* a = i *)
  rewrite h. rewrite (nth_mkseq). smt(@List Bl.t_valid). simplify.  have : exp aL 1 = aL. smt(@Bl.ZP.ZModE).
  move => h'. rewrite h'. simplify. apply not_inv.
  (* a <> i *)
  rewrite (nth_mkseq). smt(@List Bl.t_valid). simplify.  have : exp aL 1 = aL. smt(@Bl.ZP.ZModE).
  move => h'. rewrite h'. have : Bl.GB.g ^ result_R.`2 <>
      Bl.GB.g ^  aL. apply (contraNneq false). move => h''. apply h.
      rewrite Bl.exp_GB_can in h''. trivial. trivial.
  move => h''. rewrite h''. simplify. apply (contraNneq false). move => h'''.
      apply h. smt(@Bl.ZP.ZModE). trivial.
    
  (* starting goal 2, d correct *)
  case (result_R.`2 = aL); move => h.
  (* a = i *)
  rewrite h. rewrite (nth_mkseq). smt(Bl.t_valid). simplify. have : exp aL 1 = aL. smt(@Bl.ZP.ZModE).
move => h'. rewrite h'. simplify.
  have : one / (aL + (one - aL)) = one.
  smt(@Bl.ZP.ZModE). move => h''. rewrite h''.
  smt(@Bl.ZP.ZModE @Bl.GB @Bl.ZP).
      (* a <> i *)

rewrite (nth_mkseq). smt(Bl.t_valid). simplify.
  have : exp aL 1 = aL. smt(@Bl.ZP.ZModE).
  move => h'. rewrite h'.
  have : Bl.GB.g ^ result_R.`2 <> Bl.GB.g ^ aL.
  + apply (contraNneq false). move => h''. apply h.
      rewrite Bl.exp_GB_can in h''. exact h''.

      smt().
 
    move => h''. rewrite h''. simplify.

    
  rewrite H1 in H2. rewrite Bl.GT_shuffle2 in H2. 
      rewrite mkKey_ga in H2.


 
      rewrite -Bl.ZP_GT.expB in H2.


    rewrite -Bl.ZP.expB in H2. 

  rewrite Bl.e_div1 in H2.
pose R   := Bl.GB.( * ) result_R.`4 (Bl.GB.inv result_R.`6).
pose a   := aL - result_R.`2.
pose b   := result_R.`5 - result_R.`3.



have hRa : R ^ a = Bl.GB.g ^ b.
+ apply (Bl.e_inj1 _ _ Bl.GB.g); first exact Bl.g_neq_e.
  rewrite !Bl.e_pow1 Bl.e_g_g -Bl.e_pow2.
  exact H2.

have nz_a : a <> Bl.ZP.ZModE.zero by rewrite /a; smt(@Bl.ZP.ZModE).
have nz_b : b <> Bl.ZP.ZModE.zero by rewrite /b; smt(@Bl.ZP.ZModE).
pose xR := Bl.ZP.loge R.
have hRexp : R = Bl.GB.g ^ xR by rewrite /xR Bl.ZP.expgK.

have hxR : Bl.ZP.ZModE.( * ) xR a = b.
+ have := hRa. rewrite {1}hRexp -Bl.ZP.expM. by move/Bl.exp_GB_can.

rewrite hRexp -Bl.ZP.expM.
  apply Bl.exp_GB_can.
smt(@Bl.ZP.ZModE @Bl.ZP.ZModE.ZModpField).

    smt ().
smt().
qed.

section Hiding.
(* The proof is reasonably complicated, we start by bounding the chance
  the advesary misbehaves or computes an evaluation point for the key *)

(*fixed*)
module HidingWithBad (A : AdvH) = {
   var bad : bool
  
  proc main() : bool = {
    var phi, a, key, c, d, js, phiis, j, i0, phi0, psi, w, temp1, temp2, ws, i, phii;
    phi <$ dpoly Bl.t coeff_sample;                        
    a <$ Bl.FD.dt;                                         
    key <- Bl.mkKey a;                                              
    (c, d) <- (prodEx key phi, tt);                            
    js <@ A.choose(key, c);
      if (a \in js) {
      bad <- true;
    } else {
      bad <- false;    
    }
    phiis <- map (fun (x1 : Bl.ZP.exp) => peval phi x1) js;
    ws <- [];                                              
    j <- 0;                                                
    while (j < Bl.t - 1) {                                                 
      i0 <- nth zero js j;                                                                            
      phi0 <- peval phi i0;                                 
      psi <- (edivpoly phi (X - polyC i0)).`1;              
      w <- prodEx key psi;                                  
     (temp1, temp2) <- (phi0, w);                         
      ws <- temp2 :: ws;                                   
      j <- j + 1;                                          
    }                                                     
    (i, phii) <@ A.guess(phiis, ws);                       
    return  (phii = peval phi i /\
   ! (i \in js) /\ size js = Bl.t - 1 /\ uniq js);
  }
}.

(* EasyCrypt does not great support for sampling without replcament so we define the op axiomaticly *)
op js'_sample : exp -> exp list distr.
axiom js'_sample_ll a : is_lossless (js'_sample a).
axiom js'_sample_size a j : j \in js'_sample a=> size j = Bl.t -1.
axiom js'_uniq j a :j \in js'_sample a => uniq (a :: j).

  (* We introduce a new game which is close the to DL reduction in the first half and the old game in the second half *)

(*fixed*)
module HidingWithBad2 (A : AdvH) = {
   var bad : bool
  
  proc main() : bool = {
    var phi, a,x, key, ga, js, js', phiis, phiis', j, i0, phi0, psi, w, temp1, temp2, ws, i, phii;
    a <$ Bl.FD.dt;                                         
    key <- Bl.mkKey a;                                              
    x <$ Bl.FD.dt;  
    ga <- Bl.GB.g ^ x;  
    js <@ A.choose(key, ga);
    phiis' <$ dlist Bl.FD.dt (Bl.t-1);
      if (a \in js) {
      bad <- true;
    } else {
      bad <- false;    
    }
    js' <$ js'_sample a;
    phi <- interpolate (a::js')(x::phiis');
    phiis <- map (fun (x1 : Bl.ZP.exp) => peval phi x1) js;
    ws <- [];                                              
    j <- 0;                                                
    while (j < Bl.t - 1) {                                                 
      i0 <- nth zero js j;                                                                            
      phi0 <- peval phi i0;                                 
      psi <- (edivpoly phi (X - polyC i0)).`1;              
      w <- prodEx key psi;                                  
     (temp1, temp2) <- (phi0, w);                         
      ws <- temp2 :: ws;                                   
      j <- j + 1;                                          
    }                                                     
    (i, phii) <@ A.guess(phiis, ws);                       
    return  (phii = peval phi i /\
   ! (i \in js) /\ size js = Bl.t - 1 /\ uniq js);
  }
}.

declare module A <: AdvH {-HidingWithBad.bad, -HidingWithBad2.bad}.

lemma Ad3_split &m :
    Pr[HidingWithBad(A).main() @ &m : res] 
      <= Pr[HidingWithBad(A).main() @ &m : res /\ !HidingWithBad.bad] + Pr[HidingWithBad(A).main() @ &m : HidingWithBad.bad].
proof.
  byequiv. proc. wp. call(_:true). while (={key,phi,j,ws,c,phiis,a,js}). auto.  progress. wp.
  call(_:true). auto. auto.
qed.



(*fixed*)
module Adv3 (Adv : AdvH) : Bl.TsdhAdv = {

  proc comp(ga: Bl.GB.group list) : exp * Bl.GB.group = {

    var phi, key, c, d;
    var js, phiis, ws;
    var j, i0, phi0, psi, w;
    var temp1, temp2;
    var i, phii;
    var a;

    phi <$ dpoly Bl.t coeff_sample;
    key <- ga;

    (c, d) <- (prodEx key phi, tt);

    js <@ Adv.choose(key, c);

    phiis <- map (fun (x1 : Bl.ZP.exp) => peval phi x1) js;

    ws <- [];
    j <- 0;

    while (j < Bl.t - 1) {

      i0 <- nth zero js j;

      phi0 <- peval phi i0;

      psi <- (edivpoly phi (X - polyC i0)).`1;

      w <- prodEx key psi;

      (temp1, temp2) <- (phi0, w);

      ws <- temp2 :: ws;

      j <- j + 1;
    }

    (i, phii) <@ Adv.guess(phiis, ws);

    a <- nth zero js
          (find (fun x => Bl.GB.g ^ x = nth Bl.GB.g ga 1) js);

    return (one - a, Bl.GB.g);
  }

}.


(*fixed*)
lemma Ad3_bad_prob &m :
  Pr[HidingWithBad(A).main() @ &m : HidingWithBad.bad] <= Pr[Bl.Tsdh(Adv3(A)).main() @ &m : res] .
proof. 
  byequiv. proc. inline *. swap{1} 1 2. seq 4 6 : (={glob A, a,key,phi} /\ c{1} = c0{2} /\ d{1} = d0{2} /\ ga{2} = Bl.mkKey a{2}).
  auto. progress. wp. call(_:true).
while( ={a, key, phi, j,ws,phiis,js } /\ c{1} = c0{2} /\ d{1} = d0{2} /\ HidingWithBad.bad{1} = a{1} \in js{1}).
  auto. progress. auto. call(_:true). auto. progress. rewrite nth_mkseq. smt(Bl.t_valid). simplify.
  (* now to show equivlants of condiitions *)
  have : exp a{2} 1 = a{2}. smt(@Bl.ZP.ZModE). move => g. rewrite g.
  pose x := nth zero result_R  (find (fun (x : Bl.ZP.exp) => Bl.GB.g ^ x = Bl.GB.g ^ a{2}) result_R).
  have : x = a{2}. have : Bl.GB.g ^ x  = Bl.GB.g ^ a{2}. smt(@List). smt(@Bl).
  move => h''. rewrite h''. smt(@Bl.ZP.ZModE.ZModpField). rewrite nth_mkseq. smt(Bl.t_valid).
  have : exp a{2} 1 = a{2}. smt(@Bl.ZP.ZModE). move => g. simplify. rewrite g.
   pose x := nth zero result_R  (find (fun (x : Bl.ZP.exp) => Bl.GB.g ^ x = Bl.GB.g ^ a{2}) result_R).
   have : x = a{2}. have : Bl.GB.g ^ x  = Bl.GB.g ^ a{2}. smt(@List). smt(@Bl).
   move => h''. rewrite h''. have : a{2} + (one - a{2}) = one. smt(@Bl.ZP.ZModE.ZModpField). move => g'. rewrite g'.
      smt(@Bl.GB @Bl.ZP.ZModE). smt().  smt(). 
qed. 
  
    (* we have now dealt with the case where the adverary learns an evaluation point from the key *)







(*fixed*)
lemma real_bad &m :
    Pr[Hiding(PolyComDLScheme, A).real() @ &m : res] = Pr[HidingWithBad(A).main() @ &m : res].
proof.
  byequiv => //. proc. inline *.
  wp. call (_: true).
  while (={j, ws, key, phi, js, phiis}).
  - wp; skip => /> &2.
    pose i := nth zero js{2} j{2}.
    have h_adj := polyRemThem_adj phi{2} i.
    have h_r   := polyRemThem_r   phi{2} i.
    have heq :
      phi{2} - polyC (peval phi{2} i)
      = (edivpoly phi{2} (X - polyC i)).`1 * (X - polyC i)
      by rewrite h_r; exact h_adj.
    have hquot :
      (edivpoly (phi{2} - polyC (peval phi{2} i)) (X - polyC i)).`1
      = (edivpoly phi{2} (X - polyC i)).`1.
    + rewrite heq. apply ediv_mul_qut. apply Xi_neq_0.
    smt().
        wp.
       wp. call (_: true). wp. rnd. wp. rnd. skip. progress.

qed.



  (*fixed*)
module AdvHtoDL (A : AdvH) : Bl.DLogAdv = {
  proc guess(ga : Bl.GB.group) = {
    var a, key; (* The secret and commitment scheme key *)
      var i, phii : exp; (* Adversary's response *)
      var js; (* opening to the commitment and list of point evaludated *)
      var phiis : exp list; (* eval at the points in js *)
      var ws : Bl.GB.group list; (* witness to evaluation *)
      var temp2;
      var j : int;

      a   <$ Bl.FD.dt;
      key <- Bl.mkKey a;
    
      (* construct evaluation points *)
      js <@ A.choose(key,ga);
      phiis <$ dlist Bl.FD.dt (Bl.t-1);
    
      ws <- [];
      j <- 0;
      while (j < Bl.t -1) {
        temp2 <- (Bl.GB.(/) ga (Bl.GB.g^  (nth zero phiis j)))^(one/(a-(nth zero js j)));
          ws <- temp2 :: ws;
        j <- j + 1;      
      }

      (* Need to construct a commitment (c, d) <- (prodEx key m, tt); *)

      (i, phii) <@ A.guess(phiis,ws);

      return  peval (interpolate (i :: js) (phii :: phiis)) a;
  }
}.

(*taken from addPoly*)
axiom interpolate_prob3 phi j js : mu1 (dpoly Bl.t Bl.FD.dt) phi =
mu1 (dlet Bl.FD.dt (fun x0 => dmap (dlist Bl.FD.dt (Bl.t - 1))
  (fun (phiis'0 : Bl.ZP.exp list) => (x0, phiis'0)))) (peval phi j, map (peval phi) js).

(*taken from addPoly*)
lemma interpolate_in_dpoly js phis t : size js = t => size phis = t =>
    interpolate js phis \in dpoly t Bl.FD.dt.
proof.
move => h0 h1. rewrite supp_dpoly. smt(@List). split. rewrite -h0. apply interpolate_deg; trivial. smt(). smt(@Poly @Bl.FD).
qed.


(*taken from addPoly*)
lemma interpolate_corr2 js phiis : uniq js => size js = size phiis => map (fun x => peval (interpolate js phiis) x) js = phiis.
    move => h h'. pose phi := interpolate js phiis. rewrite eq_sym. apply interpolate_corr; trivial.
    apply interpolate_deg; trivial.
qed.

(*taken from addPoly*)
lemma interpolate_corr2_head j js phi phis :  uniq (j :: js) => size js = size phis =>
    peval (interpolate (j :: js) (phi :: phis)) j = phi.
    move => h h'. have : map (peval (interpolate (j :: js) (phi :: phis))) (j :: js) =  (phi :: phis).
    apply interpolate_corr2; trivial. smt(@List). simplify.  move => g. smt().
qed.




(*taken from addPoly*)
lemma interpolate_corr2_tail j js phi phis :  uniq (j :: js) => size js = size phis =>
    map (fun x => peval (interpolate (j :: js) (phi :: phis)) x) js = phis.
    move => h h'. have : map (peval (interpolate (j :: js) (phi :: phis))) (j :: js) =  (phi :: phis).
    apply interpolate_corr2; trivial. smt(@List). simplify.  move => g. smt().
qed.


(*taken form addPoly*)
lemma inter_inter j j' js js' x phii : size js = size phii => size js' = size phii => uniq (j :: js) =>
    interpolate (j :: js) (map (peval (interpolate (j' :: js') (x :: phii))) (j :: js)) =
    interpolate (j' :: js') (x :: phii).
proof.
  move => h0 h1 h2. apply interpolate_corr; trivial. smt(interpolate_deg). smt(@List).
qed.



(*fixed*)
lemma HidingWithBadEquiv &m :
    Pr[HidingWithBad2(A).main() @ &m : res /\ !HidingWithBad2.bad] =
    Pr[HidingWithBad(A).main() @ &m : res /\ !HidingWithBad.bad].
    proof.



      byequiv. proc. inline *. swap{1} 8 -5. swap{2} [2..3] -1. seq 3 2 : (={glob A, a, key} /\ key{1} = Bl.mkKey a{1} /\
  size js'{1} = Bl.t-1 /\ uniq (a{1} :: js'{1})). rnd{1}. auto.
  progress. apply js'_sample_ll. apply (js'_sample_size aL); trivial. smt(js'_uniq @List). smt(js'_uniq @List).

  seq 7 5 : (={glob A,a,key, phiis,phi,js} /\ HidingWithBad2.bad{1} = HidingWithBad.bad{2} /\ key{1} = Bl.mkKey a{1} /\
  uniq (a{1} :: js'{1}) /\  size js'{1} = Bl.t-1).
  swap{1} 4 -2. wp. call(_:true). wp.

  rnd (fun (x : exp * exp list) => (interpolate (a{1}::js'{1})(x.`1::x.`2)))
  (fun x=> (peval x a{1}, map (peval x) js'{1})) : 0 0. auto. progress.
  (* poly to list to poly *) rewrite eq_sym. apply interpolate_corr. rewrite dmap_id in H2.
  rewrite supp_dpoly in H2. smt(Bl.t_valid). smt(@List). smt(@List). smt(@List). smt().
    (* poly to list poly prob *) rewrite dmap_id.


    apply interpolate_prob3. 
  (* poly to list poly prob *) rewrite dmap_id. apply interpolate_in_dpoly. smt(@List).
  have :  xphiis'L.`2 \in dlist Bl.FD.dt (Bl.t - 1). clear H2 H3. rewrite supp_dlet in H4. smt(@Distr).
  move => g. smt(@List @DList Bl.t_valid). 
  (* list to poly to list *) rewrite interpolate_corr2_head. smt(@List).
  have :  xphiis'L.`2 \in dlist Bl.FD.dt (Bl.t - 1). clear H2 H3. rewrite supp_dlet in H4. smt(@Distr).
  move => g. smt(@List @DList Bl.t_valid).  
  rewrite interpolate_corr2_tail. smt(@List).
  have :  xphiis'L.`2 \in dlist Bl.FD.dt (Bl.t - 1). clear H2 H3. rewrite supp_dlet in H4. smt(@Distr).
  move => g. smt(@List @DList Bl.t_valid). smt(). rewrite comPolEval. smt(interpolate_deg @List).
  rewrite interpolate_corr2_head. smt(@List). smt(@List). trivial.
  
  (* finishing up *)
  call(_:true). while (={glob A, a, key, phiis, phi, js,j,ws} /\
  HidingWithBad2.bad{1} = HidingWithBad.bad{2} /\
    key{1} = (Bl.mkKey a{1})%Bl /\ uniq (a{1} :: js'{1}) /\ size js'{1} = Bl.t - 1). auto. progress.
  auto. auto. auto.
  qed.


(*taken form add Poly*)
lemma inter_inter_tail a x js js'0 phi : size js'0 = size phi => size js = size phi =>
    uniq (a :: js) => uniq (a :: js'0) =>
    interpolate (a :: js) (x :: map (peval (interpolate (a :: js'0) (x :: phi))) js) =
    interpolate (a :: js'0) (x :: phi).
 proof.
  admit.
 qed.
  





lemma d_log &m :

  islossless A.guess =>  

  Pr[HidingWithBad2(A).main() @ &m : res /\ !HidingWithBad2.bad] <= 

  Pr[Bl.DLogExp(AdvHtoDL(A)).main() @ &m : res].



  proof.

   

   
  move => h. byequiv. proc. inline *. swap{2} [1..2] 2.

  seq 2 2 : (={glob A, a,key} /\ key{1} = Bl.mkKey a{1}). auto.



  seq 3 3 : (={glob A, a,key,x,ga,js} /\ key{1} = Bl.mkKey a{1}  /\ ga{2} = Bl.GB.g ^  x{2}).

  auto. call (_:true). auto.



   (* stupid case 2 *)

  case (a{1} \in js{1}). wp. call{1} (_ : true ==> true). call{2} (_ : true ==> true).

  while (={j}). auto. wp. rnd{1}. auto. progress. apply js'_sample_ll. trivial. trivial.



  (* stupid case 1 *)

  case (size js{1} <> Bl.t-1). wp. call{1} (_ : true ==> true). call{2} (_ : true ==> true).

  while (={j}). auto. wp. rnd{1}. auto. progress. trivial. apply js'_sample_ll. trivial.



  (* stupid case 3*)

  case (! uniq js{1}). wp. call{1} (_ : true ==> true). call{2} (_ : true ==> true).

  while (={j}). auto.  wp. rnd{1}. auto. progress. trivial.  apply js'_sample_ll. trivial. 



  (* The first issue is to show the evaluation of the polynomials is equvilant *)

  seq 5 1 : (={glob A, a,key,x,ga,js,phiis} /\ key{1} = Bl.mkKey a{1}  /\ ga{2} = Bl.GB.g ^ x{2} /\

  ! (a{1} \in js{1}) /\ size js{1} = Bl.t - 1 /\ uniq (a{1} :: js'{1}) /\ size phiis{1} = Bl.t-1 /\

  phi{1} = interpolate (a{2} :: js'{1}) (x{2} :: phiis'{1}) /\ size js'{1} = Bl.t-1 /\ size phiis'{1} = Bl.t - 1

  /\ uniq js{1} /\ phiis{2} = map (peval (interpolate (a{1} :: js'{1})(x{1} :: phiis'{1}))) js{1}). swap{1} 1 2.  wp.





  (* 1. Perform the random transformation *)











  rnd (fun phiis=> map (peval (interpolate (a{1}::js'{1})(x{1}::phiis))) js{1})

  (fun phiis => map (peval (interpolate (a{1} :: js{1})(x{1} :: phiis))) js'{1}). auto. progress.



    apply js'_sample_ll.

    (* left right left *) rewrite inter_inter_tail.
smt(js'_sample_size size_map @DList @List).


 smt(@DList Bl.t_valid js'_sample_size @List). 

    smt(js'_uniq). smt(@List). rewrite interpolate_corr2_tail. smt(@List). smt(@DList Bl.t_valid @List). trivial.

  (* right left right prob in *) rewrite !(AddDistr.dlist_mu1 _ _ Bl.GT.order). smt(@DList Bl.t_valid @List). smt(@Bl.FD).

    smt(@List js'_sample_size). smt(@Bl.FD). trivial. apply supp_dlist. smt(Bl.t_valid). split. smt(@List). apply allP. smt(@Bl.FD).

  (* right left right *) rewrite inter_inter_tail. smt(js'_sample_size @DList Bl.t_valid @List). smt(@DList Bl.t_valid @List). 

  smt(@List). smt(js'_uniq). rewrite interpolate_corr2_tail. smt(js'_uniq). smt(js'_sample_size @DList Bl.t_valid @List). trivial.

    smt(js'_uniq). smt(js'_uniq). smt(@List). smt(js'_sample_size). smt(@List js'_sample_size).



  (* witnesses *)

  wp. call(_:true). while (={glob A,  a, key, js, x, ga, phiis,j,ws} /\ key{1} = Bl.mkKey a{1} /\ ga{2} = Bl.GB.g ^  x{2} /\

  size js{1} = Bl.t -1 /\ 0 <= j{1} /\ ! (a{1} \in js{1}) /\ phi{1} = interpolate (a{1} :: js'{1}) (x{1} :: phiis'{1}) /\

    uniq js{1} /\ size phiis{1} = Bl.t -1 /\ size js'{1} = Bl.t-1 /\ size phiis'{1} = Bl.t-1 /\ uniq (a{1} :: js'{1}) /\

   phiis{2} = map (peval (interpolate (a{1} :: js'{1})(x{1} :: phiis'{1}))) js{1}).

    auto. progress. rewrite comPolEval. apply degDiv2. smt(interpolate_deg).


    rewrite -Bl.ZP.expB. 

rewrite (nth_map zero zero); first by smt().

  rewrite -Bl.ZP.expM.

apply Bl.exp_GB_can.


pose i := nth zero js{2} j{2}.


have a_neq_i : (-i) + a{2} <> Bl.ZP.ZModE.zero
  by rewrite /i; smt(@List @Bl.ZP.ZModE).


rewrite prt_eval; first exact a_neq_i.

have hINT_a :
  peval (interpolate (a{2} :: js'{1}) (x{2} :: phiis'{1})) a{2} = x{2}.
+ apply interpolate_corr2_head; smt(@List).
rewrite hINT_a.

smt(@Bl.ZP.ZModE @Bl.ZP.ZModE.ZModpField).


smt().

auto.
progress.

have hlist :
  result_R.`2 :: map (peval (interpolate (a{2} :: js'{1}) (x{2} :: phiis'{1}))) js{2}
  = map (peval (interpolate (a{2} :: js'{1}) (x{2} :: phiis'{1})))
        (result_R.`1 :: js{2}).
+ smt(@List).
rewrite hlist.


rewrite inter_inter.
+ smt(@List).
+ smt(@List).
+ smt(@List).
apply interpolate_corr2_head.
+ smt(@List).
+ smt(@List).

          trivial.
        trivial.



qed. 







(*fixed*)
lemma PolyComDLScheme_Hiding &m :
  islossless A.guess =>   
  Pr[Hiding(PolyComDLScheme, A).real() @ &m : res] <=
  Pr[Bl.DLogExp(AdvHtoDL(A)).main() @ &m : res] + 
  Pr[Bl.Tsdh(Adv3(A)).main() @ &m : res].
proof.
 move => h. rewrite real_bad. have : forall (b a c : real), a <= b => b <= c => a <= c. smt(). move=> h'.
   apply (h' (Pr[HidingWithBad(A).main() @ &m : res /\ !HidingWithBad.bad] + Pr[HidingWithBad(A).main() @ &m : HidingWithBad.bad])).
   apply Ad3_split. have : forall (a a' b b':real), a <= a' => b <= b' => a + b <= a' + b'. smt().
   move => g. apply g. rewrite -HidingWithBadEquiv.  apply d_log; trivial. apply Ad3_bad_prob.
 qed.


end section Hiding.




