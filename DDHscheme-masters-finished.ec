(* Part of a masters thesis written at NTNU, by Morten Solberg *)

(*** Require and import the need theories ***)
require import AllCore DBool Distr CyclicGroup StdOrder Dexcepted StdBigop. 
(*   *) import RealOrder Bigreal. 

(*** Remove the prover Alt-Ergo due to a bug ***)
prover [-"Alt-Ergo"].  

(*** Construct a full, lossless, uniform distribution of group elements ***)
op dG : { group distr | is_lossless dG /\ is_full dG /\ is_uniform dG } as dG_luf. 
lemma dG_ful : is_lossless dG /\ is_full dG /\ is_uniform dG by []. 
axiom dG_size : forall (a:group), mu1 dG a = 1%r/q%r. 

lemma dG_full : forall (a:group), a \in dG. 
proof. 
move => a. 
have H0 : is_full dG by smt(dG_ful).  
smt(). 
qed. 

(*** Declare the types we use in the proof ***)
type X = group * group.
type W = t.
type K = t * t.
type S = group.
type Y = group.

(*** Define the types for the plaintexts, ciphertexts and keys ***)
type pkey = group * group * group.
type skey = K.
type plaintext = group.
type ciphertext = group * group * group. 

(*** Module simply sampling y at random and returning y ***)
module Yrand = {
  proc main(s:group) : Y = {
    var y;
    y <$ dG;
    return y;
  }
}.

(*** Proof that the distribution dG is uniform when sampling y ***)
lemma Yrand_pr &m : forall(y s : group), Pr[Yrand.main(s) @ &m : res = y] = 1%r/F.q%r. 
proof. 
move => y s. 
byphoare => //. 
proc. rnd (pred1 y). skip. 
progress. smt(dG_size). smt(). 
qed. 

(*** Module computing the hash value of (x0, x1) not in ls ***)
module Ycomp = {
  proc main(s:group, w w' r : t) : Y = {
    var  x0, x1, k0, k1, y; 
    k1 <$ FDistr.dt;
    x0 <- g^w;
    x1 <- g^r^(w+w');
    k0 <- log s - k1 * r;
    y <- x0^k0*x1^k1;
    return y;
  }
}.

(*** Proof that the distribution of x0^k0*x1^k1 is uniform when (x0, x1) not in ls ***)
lemma Ycomp_pr &m  : forall(y s : group, r w w' : t), w <> F.zero /\ w' <> F.zero /\ r <> F.zero => Pr[Ycomp.main(s, w, w', r) @ &m : res = y] = 1%r/F.q%r. 
proof. 
progress.  
byphoare (_: arg = (s, w, w', r) /\ r <> F.zero /\ w <> F.zero /\ w' <> F.zero ==> _) => //=.
proc.  wp.  progress. 
conseq (_: _ ==> k1 = (log y - w*log s)/(r*(w+w') - r*w)). progress.   
  rewrite pow_pow pow_pow pow_pow. 
rewrite log_mul. rewrite log_pow log_pow.
have -> : (log g) = F.one by smt(@CyclicGroup). 
have -> : F.one * (w{hr} * (log s{hr} - k10 * r{hr})) = (w{hr} * (log s{hr} - k10 * r{hr})) by smt. 
have -> : F.one * (r{hr} * ((w{hr} + w'{hr}) * k10)) = (r{hr} * ((w{hr} + w'{hr}) * k10)) by smt. 
have -> : (w{hr} * (log s{hr} - k10 * r{hr})) = w{hr} * log s{hr} - w{hr} * k10 * r{hr}.    
smt(@CyclicGroup).  
have -> : (w{hr} * log s{hr} - w{hr} * k10 * r{hr} + r{hr} * ((w{hr} + w'{hr}) * k10) -
 w{hr} * log s{hr}) =  - w{hr} * k10 * r{hr} + r{hr} * ((w{hr} + w'{hr}) * k10) by smt. 
rewrite addC. 
have -> : (r{hr} * (w{hr} + w'{hr}) - r{hr} * w{hr}) = r{hr} * w'{hr}. 
rewrite -mulfDl. rewrite addC. field.
field. smt. 
rewrite pow_pow pow_pow pow_pow.  
algebra.   smt. 
rnd . auto. progress. rewrite FDistr.dt1E. smt.  
qed. 


(*** General module type for a PKE ***)
module type Scheme = {
  proc keygen() : pkey * skey
  proc encrypt(pk:pkey, m:plaintext) : ciphertext
  proc decrypt(sk:skey, c:ciphertext) : plaintext
}.

(*** Concrete construction of the encryption scheme ***)
module DDHscheme : Scheme = {
  proc keygen() : pkey * skey = {
    var k0, k1, g', s, r, pk, sk;
    k0 <$ FDistr.dt; k1 <$ FDistr.dt; r <$ FDistr.dt;
    g' <- g^r;
    s  <- g^k0 * g'^k1;
    pk <- (g, g', s);
    sk <- (k0, k1);
    return (pk, sk);
  }

  proc encrypt(pk:pkey, m:plaintext) : ciphertext = {
    var x0, x1, y, e, c, w;
    w <$ FDistr.dt;
    x0 <- pk.`1^w; x1 <- pk.`2^w;
    y <- pk.`3^w;
    e <- m * y;
    c <- (x0, x1, e);
    return c;
  }

  proc decrypt(sk:skey, c:ciphertext) : plaintext = {
    var m', y;
    y <- c.`1^sk.`1 * c.`2^sk.`2;
    m' <- c.`3 / y;
    return m';
  }
}.

(*** Proof of correctness for the above scheme ***)
module Correctness = {
  proc main(m:plaintext) : bool = {
    var pk, sk, m', c;
    (pk, sk) <- DDHscheme.keygen();
       c     <- DDHscheme.encrypt(pk,m);
       m'    <- DDHscheme.decrypt(sk,c);
    return (m = m');
  }
}.

lemma correct : hoare[Correctness.main : true ==> res]. 
proof. 
proc. 
inline*; auto. 
progress. 
have -> : m{hr} * (g ^ k0 * g ^ r0 ^ k10) ^ w0 / (g ^ w0 ^ k0 * g ^ r0 ^ w0 ^ k10) = m{hr} * g1. 
rewrite -pow_mul. rewrite pow_pow pow_pow pow_pow pow_pow pow_pow pow_pow. 
have -> : (g ^ (k0 * w0) * g ^ (r0 * (k10 * w0))) = (g ^ (w0 * k0) * g ^ (r0 * (w0 * k10))).    
smt(@CyclicGroup). rewrite -div_def. rewrite log_mul.  
have -> : g ^
(log m{hr} + log (g ^ (w0 * k0) * g ^ (r0 * (w0 * k10))) -
 log (g ^ (w0 * k0) * g ^ (r0 * (w0 * k10)))) = g ^ (log m{hr}). smt. 
rewrite gpow_log. 
rewrite -mul1. smt(@CyclicGroup).  smt(@CyclicGroup). 
qed. 

(*** Construct an abstract CPA adversary ***)
module type CPAadversary = {
  proc choose(pk:pkey)     : plaintext * plaintext
  proc guess(c:ciphertext) : bool
}.

(*** The original CPA attack ***)
module CPA(S:Scheme, A:CPAadversary) = {
  proc main() : bool = {
    var pk, sk, m0, m1, c, b, b';
    (pk,sk)  <- S.keygen();
    (m0,m1)  <- A.choose(pk);
       b     <$ {0,1};
       c     <- S.encrypt(pk, b?m1:m0);
       b'    <- A.guess(c);
    return (b = b');
  }
}.

(*** Define a smoothness adversary ***) 
module type SmoothAdversary = {
  proc guess(x0 x1 g g' s y : group) : bool
}.

module Smooth1(A:SmoothAdversary) = {
  proc main() : bool = {
    var x0, x1, k0, k1, a, g', s, b, w, w', y;
    a <$ FDistr.dt; g' <- g^a;
    w <$ FDistr.dt; w' <$ FDistr.dt \ (pred1 F.zero);
    x0 <- g^w; x1 <- g'^(w + w');
    k0 <$ FDistr.dt; k1 <$ FDistr.dt;
    s <- g^k0*g'^k1;
    y <- x0^k0*x1^k1;
    b <- A.guess(x0, x1, g, g', s, y);
    return b;
  }
}.

module Smooth0(A:SmoothAdversary) = {
  proc main() : bool = {
    var x0, x1, k0, k1, a, g', s, b, w, w', y;
    a <$ FDistr.dt; g' <- g^a;
    w <$ FDistr.dt; w' <$ FDistr.dt \ (pred1 F.zero);
    x0 <- g^w; x1 <- g'^(w + w');
    k0 <$ FDistr.dt; k1 <$ FDistr.dt;
    s <- g^k0*g'^k1;
    y <$ dG;
    b <- A.guess(x0, x1, g, g', s, y);
    return b;
  }
}.

module SmoothAdv(A:CPAadversary) = {
  proc guess(x0, x1, g, g', s, y) = {
    var m0, m1, b, b';
    (m0, m1) <- A.choose(g, g', s);
       b     <$ {0,1};
       b'    <- A.guess(x0, x1, (b?m1:m0) * y);
    return (b = b');
  }
}.

(*** Construct a DDH adversary ***)
module type DDHadversary = {
  proc guess(g g' s x0 x1 y : group) : bool
}.

module DDH1(A:DDHadversary) = {
  proc main() : bool = {
    var r, g', x0, x1, b, w, k0, k1, s, y;
    r <$ FDistr.dt; g' <- g^r;
    w <$ FDistr.dt;
    k0 <$ FDistr.dt; k1 <$ FDistr.dt;
    s <- g^k0*g'^k1;
    x0 <- g^w; x1 <- g'^w;
    y <- x0^k0*x1^k1;
    b <- A.guess(g, g', s, x0, x1, y);
    return b;
  }
}.

module DDH0(A:DDHadversary) = {
  proc main() : bool = {
    var r, g', x0, x1, b, w, w', k0, k1, s, y;
    r <$ FDistr.dt; g' <- g^r;
    w <$ FDistr.dt; w' <$ FDistr.dt \ (pred1 F.zero);
    k0 <$ FDistr.dt; k1 <$ FDistr.dt;
    s <- g^k0*g'^k1;
    x0 <- g^w; x1 <- g'^(w+w');
    y <- x0^k0*x1^k1; 
    b <- A.guess(g, g', s, x0, x1, y);
    return b;
  }
}.  

module DDHadv(A:CPAadversary) = {
  proc guess(g, g', s, x0, x1, y) : bool = {
  var m0, m1, b, b';
  (m0, m1) <- A.choose(g, g', s);
     b     <$ {0,1};
     b'    <- A.guess(x0, x1, (b?m1:m0) * y);
  return (b = b');
  }
}.

(*** Start of the security proof ***)
section Security. 
(*** Define an abstract adversary of type CPAadversary ***)
declare module A:CPAadversary. 
(*** Axioms making sure the procedures of the adversary terminate ***)
axiom Ac_ll : islossless A.choose. 
axiom Ag_ll : islossless A.guess. 

(*** Perfect simulation of the original attack ***)
local module Game1(A:CPAadversary) = {
  proc main() : bool = {
    var  w, pk, sk, m0, m1, b, b', y, e, c, x0, x1;
    (pk, sk) <- DDHscheme.keygen();
       w     <$ FDistr.dt;
    x0 <- pk.`1^w; x1 <- pk.`2^w;
    (m0, m1) <- A.choose(pk);
    b       <$ {0,1};
    y       <- x0^sk.`1 * x1^sk.`2;
    e       <- (b?m1:m0) * y;
    c <- (x0,x1,e);
    b'      <- A.guess(c);
    return (b = b'); 
  }
}.

(*** Proof that the simulation above is equivalent to the original attack ***)
local equiv CPA_Game1 : CPA(DDHscheme, A).main ~ Game1(A).main : ={glob A} ==> ={res}. 
proof. 
proc;inline*. 
call(_:true). swap{2} [9 .. 11] 1. swap{2} 13 -3.  
wp. rnd. 
wp. 
rnd. call(_:true). 
auto. progress. rewrite -pow_mul. rewrite pow_pow pow_pow pow_pow pow_pow pow_pow pow_pow. 
have -> : k0L * wL = wL * k0L by smt. 
have -> : k1L * wL = wL * k1L by smt. 
trivial. 
qed.  

local lemma CPA_Game1_pr &m : Pr[CPA(DDHscheme,A).main() @ &m : res] = Pr[Game1(A).main() @ &m : res] by byequiv CPA_Game1. 

(*** Game2: sample x from X \ L instead of L ***)
local module Game2(A:CPAadversary) = {
  proc main() : bool = {
    var  w, w', pk, sk, m0, m1, b, b', y, e, c, x0, x1;
    (pk, sk) <- DDHscheme.keygen();
       w     <$ FDistr.dt; w' <$ FDistr.dt \ (pred1 F.zero); 
    x0 <- pk.`1^w; x1 <- pk.`2^(w+w');
    (m0, m1) <- A.choose(pk);
    b       <$ {0,1};
    y       <- x0^sk.`1 * x1^sk.`2;
    e       <- (b?m1:m0) * y;
    c <- (x0,x1,e);
    b'      <- A.guess(c);
    return (b = b'); 
  }
}.

(*** Proofs that distinguishing between the two experiments above is equivalent to 
   distinguishing between a DDH tuple and a random tuple ***)
local equiv Game1_DDH1 : Game1(A).main ~ DDH1(DDHadv(A)).main : ={glob A} ==> ={res}. 
proof. 
proc;inline*. 
wp.
call(_:true). swap{2} [4 .. 5] -3. swap{1} 9 -4. swap{2} 9 5. swap{2} [14 .. 15] 2. 
wp; rnd. call(_:true). auto. 
qed. 

local lemma Game1_DDH1_pr &m : Pr[Game1(A).main() @ &m : res] = Pr[DDH1(DDHadv(A)).main() @ &m : res] by byequiv Game1_DDH1. 

local equiv Game2_DDH0 : Game2(A).main ~ DDH0(DDHadv(A)).main : ={glob A} ==> ={res}. 
proof. 
proc;inline*;wp. 
call(_:true). 
swap{2} [5 .. 6] -4. swap{1} [9 .. 10] -4. swap{2} 10 5. swap{2} [15 .. 16] 2. 
wp;rnd. 
call(_:true); auto. 
qed. 

local lemma Game2_DDH0_pr &m : Pr[Game2(A).main() @ &m : res] = Pr[DDH0(DDHadv(A)).main() @ &m : res] by byequiv Game2_DDH0. 

(*** Game3: sample y at random from the group instead of computing y <- x0^k0*x1^k1 ***)
local module Game3(A:CPAadversary) = {
  proc main() : bool = {
    var  w, w', pk, sk, m0, m1, b, b', y, e, c, x0, x1;
    (pk, sk) <- DDHscheme.keygen();
       w     <$ FDistr.dt; w' <$ FDistr.dt \ (pred1 F.zero); 
    x0 <- pk.`1^w; x1 <- pk.`2^(w+w');
    (m0, m1) <- A.choose(pk);
    b       <$ {0,1};
    y       <$ dG;
    e       <- (b?m1:m0) * y;
    c <- (x0,x1,e);
    b'      <- A.guess(c);
    return (b = b'); 
  }
}.

(*** Proofs that distinguishing between Game2 and Game3 is equivalent to 
    breaking the smoothness assumption ***)
local equiv Game2_Smooth1 : Game2(A).main ~ Smooth1(SmoothAdv(A)).main : ={glob A} ==> ={res}.
proof. 
proc;inline*;wp. 
call(_:true). 
swap{2} [7 .. 8] -6. 
swap{1} [9 .. 10] -4. 
swap{2} 18 -4. wp.  swap{2} 14 4. rnd. call(_:true). 
wp;auto. 
qed. 

local lemma Game2_Smooth1_pr &m : Pr[Game2(A).main() @ &m : res] = Pr[Smooth1(SmoothAdv(A)).main() @ &m : res] by byequiv Game2_Smooth1. 

local equiv Game3_Smooth0 : Game3(A).main ~ Smooth0(SmoothAdv(A)).main : ={glob A} ==> ={res}. proof.  
proc;inline*;wp. 
call(_:true). wp. swap{1} 15 -5. rnd; call(_:true). swap{1} 9 -6. swap{1} 11 -7. swap{1} 5 -4. 
wp. 
rnd. swap{2} [7 .. 8] -5.  swap{2} 4 2. auto. 
qed.  

local lemma Game3_Smooth0_pr &m : Pr[Game3(A).main() @ &m : res] = Pr[Smooth0(SmoothAdv(A)).main() @ &m : res] by byequiv Game3_Smooth0.  

(*** Modify the simulator: make the adversary's output completely independent of the hidden bit b ***)
local module Game3indep(A:CPAadversary) = {
  proc main() : bool = {
    var  w, w', pk, sk, m0, m1, b, b', y, e, c, x0, x1;
    (pk, sk) <- DDHscheme.keygen();
       w     <$ FDistr.dt; w' <$ FDistr.dt \ (pred1 F.zero); 
    x0 <- pk.`1^w; x1 <- pk.`2^(w+w');
    (m0, m1) <- A.choose(pk);
    y       <$ dG;
    e       <- y;
    c <- (x0,x1,e);
    b'      <- A.guess(c);
    b       <$ {0,1};
    return (b = b'); 
  }
}.

(*** Proof that the above experiment is equivalent to Game3 ***)
local equiv Game3_Game3indep : Game3(A).main ~ Game3indep(A).main : ={glob A} ==> ={res}. 
proof. 
proc;inline*. swap{2} 18 -4. 
call(_:true). wp. 
rnd (fun y, (b?m1:m0) * y){2} (fun y, y/  (b?m1:m0)){2}. 
rnd. 
call(_:true); auto. 
progress. 
smt(@CyclicGroup). smt(dG_ful). smt(dG_ful). smt(@CyclicGroup). 
qed. 

local lemma Game3_Game3indep_pr &m : Pr[Game3(A).main() @ &m : res] = Pr[Game3indep(A).main() @ &m : res] by byequiv Game3_Game3indep. 

(*** Proof that the adversary's advantage in Game3indep is 1/2 ***)
local lemma Game3indep_half &m : Pr[Game3indep(A).main() @ &m : res] = 1%r/2%r. 
proof. 
byphoare => //. 
proc; inline*. 
rnd; call(_:true). apply Ag_ll. 
auto. call(_:true); first apply Ac_ll. 
auto. progress. smt(@CyclicGroup). smt. smt(dG_ful). smt(@DBool). 
qed. 

local lemma Game3_half &m : Pr[Game3(A).main() @ &m : res] = 1%r/2%r. 
proof. 
by rewrite (Game3_Game3indep_pr &m) (Game3indep_half &m). 
qed.  

(*** Final lemma, without us having been able to prove that the last term, 
`|Pr[Smooth1(SmoothAdv(A)).main() @ &m : res] - Pr[Smooth0(SmoothAdv(A)).main() @ &m : res]| 
is zero ***)
local lemma secure &m : 
    `|Pr[CPA(DDHscheme,A).main() @ &m : res] - 1%r/2%r| <=
    `|Pr[DDH1(DDHadv(A)).main() @ &m : res] - Pr[DDH0(DDHadv(A)).main() @ &m : res]| + 
    `|Pr[Smooth1(SmoothAdv(A)).main() @ &m : res] - Pr[Smooth0(SmoothAdv(A)).main() @ &m : res]|.
proof. 
rewrite -(Game1_DDH1_pr &m) -(Game2_DDH0_pr &m) (CPA_Game1_pr &m) -(Game2_Smooth1_pr &m) -(Game3_Smooth0_pr &m) (Game3_half &m) ler_dist_add. 
qed. 

end section Security. 
