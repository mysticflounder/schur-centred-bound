---
title: '$S(6)\le 1801$ if $R_4(3)\le 61$: a centred Schur bound and the structure at the frontier'
title-meta: "S(6) ≤ 1801 if R₄(3) ≤ 61: a centred Schur bound and the structure at the frontier"
author: Adam McKenna
date: "October 2026. doi:10.5281/zenodo.23156099"
abstract: |
  Let $S(n)$ be the Schur number and $R_k(3)$ the Ramsey number of the
  triangle in $k$ colours. We prove that $R_k(3)\le r$ implies
  $S(k+1)\le 2(k+1)\lfloor (r-1)/2\rfloor+1$. For even $r$ this is $k$ less
  than the bound $(k+1)(r-1)$ that the pigeonhole recursion and the
  inequality $S(k+1)\le R_{k+1}(3)-2$ give. Section 5 discusses the relation
  of this bound to a Schur bound of H. Wan (1997), whose proof we have not
  read. With $R_2(3)=6$ the bound gives $S(3)\le 13$, which is exact.
  Under the hypothesis $R_4(3)\le 61$, a
  computer-assisted claim of M. Tatarevic, the pigeonhole step gives
  $R_5(3)\le 302$, and the bound then gives $S(6)\le 1801$; the best
  published upper bound is $S(6)\le 1836$. We then study a Schur colouring
  of the longest interval that the bound allows. Let $R_k(3)\le u+1$,
  $(k+1)u=2t$ and $m=(k+2)t$; then the pigeonhole step and the bound give
  $S(k+2)\le 2m+1$. Let $c$ be a Schur colouring of $[1,2m+1]$ with $k+2$
  colours. Then each colour occurs exactly $t$ times in $[1,m]$. With
  $q=c(m+1)$, the neighbourhood of the centre $m$ in the
  colour $q$ is regular in every other colour, and $c(m+1-d)=c(m+1+d)$ for
  every $d\in[1,m]$ with $c(d)=q$. For six colours under $R_4(3)\le 61$, a
  Schur colouring of $[1,1801]$ gives five sets of 60 integers. Each set is
  closed under $x\mapsto 1800-x$, this map has no fixed point on it, and
  the differences of the set have at most four colours. We do not exclude
  these sets, so we do not prove $S(6)\le 1800$. The theorems are
  formalized in Lean 4 with Mathlib, with $R_4(3)\le 61$ as an explicit
  hypothesis.
---

# 1. Introduction

A set $S$ of positive integers is *sumfree* when there are no $x,y\in S$
with $x+y\in S$; the case $x=y$ is included. The Schur number $S(n)$ is the
largest $N$ such that $\{1,\dots,N\}$ is the union of $n$ sumfree sets.
Schur proved that $S(n)$ is finite [Sch16]. Only
$S(1),\dots,S(5)=1,4,13,44,160$ are known. The first three can be found by
hand [Heu18]; $S(4)=44$ is due to Baumert [Bau61] and $S(5)=160$ to Heule
[Heu18]. For $S(6)$ the published bounds are $536\le S(6)\le 1836$. The
lower bound is due to Fredricksen and Sweet [FS00]; Eliahou and Revuelta
give the upper bound as the best known one [ER21].

Let $R_k(3)$ be the least $N$ such that every colouring of the edges of the
complete graph $K_N$ with $k$ colours has a monochromatic triangle. The
inequality $S(k)\le R_k(3)-2$ is classical [Heu18, Eli20]. The known values
and bounds are $R_1(3)=3$, $R_2(3)=6$, $R_3(3)=17$ [GG55],
$51\le R_4(3)\le 62$ [Chu73, FKR04], $162\le R_5(3)\le 307$ [Exo94, Rad26]
and $R_6(3)\le 1838$ [Rad26]. The upper bounds for $R_5(3)$ and $R_6(3)$
follow from $R_4(3)\le 62$ by the pigeonhole recursion
$R_{k+1}(3)\le (k+1)(R_k(3)-1)+2$ [GG55, Rad26], and $1836=1838-2$.

M. Tatarevic has released a computer-assisted proof of $R_4(3)\le 61$ in a
public repository [Tat26]. It combines a mathematical reduction, finite
enumeration and 56,830 SAT formulas, and a Lean development in the
repository derives the bound from the unsatisfiability of these formulas
[Tat26, Chk26]. For these formulas the repository publishes solver UNSAT
records, not LRAT certificates. The author's project made and checked LRAT
certificates for all 56,830 formulas, with AI assistance; the record is
[Chk26], an issue that the author posted in the repository on 2 October
2026. For each formula an UNSAT proof was made with CaDiCaL and converted
to LRAT with drat-trim where necessary, and the checker lrat-check accepted
all 56,830 LRAT proofs. A second check by Claude (Anthropic), which used
none of the code of the first pipeline, verified the same LRAT proofs with
the CakeML-verified checker cake_lpr (56,830 of 56,830). These checks rely
on the builds of the checkers and on Tatarevic's Lean emitters that produce
the formulas, and they do not review the reduction by hand. We know of no
preprint or refereed publication of this result (Section 5). In this paper
$R_4(3)\le 61$ is a hypothesis, and every statement that uses it says so.

We prove the following.

**Theorem 1.1.** Let $k,r\ge 1$. If $R_k(3)\le r$, then
$$S(k+1)\le 2(k+1)\left\lfloor \frac{r-1}{2}\right\rfloor+1.$$

**Corollary 1.2.** (a) $S(3)\le 13$. (b) If $R_4(3)\le 61$, then
$R_5(3)\le 302$ and $S(6)\le 1801$.

The proof of Theorem 1.1 (Section 3) places a large part of one colour
class symmetrically about the centre of the interval and applies the
bound on $R_k(3)$ to the points obtained (see Section 5 on its relation to
[Wan97]). From the same hypothesis $R_4(3)\le 61$, other methods give
$S(6)\le 1805$ and $S(6)\le 1806$ (Section 3.3).

Let $R_k(3)\le 2t+2$ and $m=(k+1)t$. Then Theorem 1.1 gives
$S(k+1)\le 2m+1$. Section 4 describes a Schur colouring of the interval
$[1,2m+1]$, which we call the *frontier interval*. Each colour occurs
exactly $t$ times in $[1,m]$ (Theorem 4.1). With $k+2$ colours and two
consecutive Ramsey bounds that meet (Section 4.2), the neighbourhood of the
centre in one colour is regular in each other colour (Theorem 4.4), the
colouring is reflected about $m+1$ at the points of that colour
(Theorem 4.7), and the neighbourhoods of the endpoint split into pairs
(Theorem 4.9). For six colours this gives the following.

**Theorem 1.3** (Theorem 4.11, informal). Suppose $R_4(3)\le 61$ and
$S(6)\ge 1801$. Then a Schur colouring of $[1,1801]$ with six colours
gives five sets of 60 integers. Each set is closed under $x\mapsto 1800-x$,
this map has no fixed point on it, and the differences of two distinct
elements of the set have at most four colours.

Theorem 1.3 does not prove $S(6)\le 1800$. Whether five sets with these
properties can exist is open.

All theorems of Sections 2 to 4 are formalized in Lean 4 with Mathlib
(Section 6). Section 5 lists the literature that we checked. We make no
claim of novelty.

# 2. Definitions and lemmas

All numbers are integers, $[a,b]=\{x:\ a\le x\le b\}$, and $|x-y|$ is the
distance of $x$ and $y$.

A set $X$ of positive integers is *covered by $n$ sumfree sets* when there
are sumfree sets $C_1,\dots,C_n$ with $X\subseteq C_1\cup\dots\cup C_n$. The
sets need not be disjoint or contained in $X$. A subset of a sumfree set is
sumfree, so $S(n)$ is also the largest $N$ such that $[1,N]$ is covered by
$n$ sumfree sets. If $[1,M+1]$ is not covered by $n$ sumfree sets, then
$S(n)\le M$.

We write $R_k(3)\le r$ for the statement: for every set $V$ of at least $r$
points and every colouring of the pairs of points of $V$ with at most $k$
colours, there is a monochromatic triangle.

Let $n\ge1$. A *Schur colouring of $[1,N]$ with $n$ colours* is a map $c$
from $[1,N]$ to a set of $n$ colours such that there are no $x,y\ge 1$ with
$x+y\le N$ and $c(x)=c(y)=c(x+y)$; the case $x=y$ is included.

**Lemma 2.1.** Let $n\ge 1$.

(a) If $c$ is a Schur colouring of $[1,N]$ with $n$ colours, then its $n$
colour classes are sumfree sets that cover $[1,N]$.

(b) If the sumfree sets $C_1,\dots,C_n$ cover $[1,N]$, then a map $c$ that
gives each $x\in[1,N]$ an index $i$ with $x\in C_i$ is a Schur colouring of
$[1,N]$ with $n$ colours.

**Proof.** (a) A colour class is a subset of $[1,N]$, and three elements
$x$, $y$, $x+y$ of one class are excluded by the definition. (b) If
$c(x)=c(y)=c(x+y)=i$, then $x,y,x+y\in C_i$, which is false. $\square$

**The difference colouring.** Let $c$ be a Schur colouring of $[1,N]$. Give
each pair $\{x,y\}$ of distinct points of $[0,N]$ the colour $c(|x-y|)$;
this is defined, since $1\le |x-y|\le N$.

**Lemma 2.2.** The difference colouring has no monochromatic triangle.

**Proof.** Let $x<y<z$ be points of $[0,N]$. The numbers $y-x$, $z-y$ and
$z-x$ lie in $[1,N]$, and $(y-x)+(z-y)=z-x$. So they do not all have the
same colour. $\square$

**Lemma 2.3.** Let $c$ be a Schur colouring of $[1,N]$, let
$V\subseteq[0,N]$, and let $K$ be a set of at most $k$ colours with
$c(|x-y|)\in K$ for all distinct $x,y\in V$. If $R_k(3)\le r$, then
$|V|<r$.

**Proof.** Otherwise the difference colouring on $V$ uses at most $k$
colours on at least $r$ points, and it has a monochromatic triangle. This
contradicts Lemma 2.2. $\square$

For a finite set $V\subseteq[0,N]$, a point $v$ and a colour $i$, the
*colour-$i$ neighbourhood* of $v$ in $V$ is
$$\Gamma_i(v;V)=\{w\in V:\ w\ne v,\ c(|v-w|)=i\}.$$
The sets $\Gamma_i(v;V)$, for all colours $i$, partition $V\setminus\{v\}$.

**Lemma 2.4.** Let $c$ be a Schur colouring of $[1,N]$, let
$V\subseteq[0,N]$ and $v\in[0,N]$, and let $i$ be a colour. If $x$ and $y$
are distinct points of $\Gamma_i(v;V)$, then $c(|x-y|)\ne i$.

**Proof.** The points $v$, $x$ and $y$ are distinct points of $[0,N]$, and
the pairs $\{v,x\}$ and $\{v,y\}$ have the colour $i$. If $\{x,y\}$ also had
the colour $i$, the three points would form a monochromatic triangle, which
contradicts Lemma 2.2. $\square$

**Lemma 2.5** (pigeonhole step [GG55]). Let $k,N\ge 1$. If $R_k(3)\le N$,
then $R_{k+1}(3)\le (k+1)(N-1)+2$.

**Proof.** Let $V$ be a set of at least $(k+1)(N-1)+2$ points whose pairs
have at most $k+1$ colours, and fix $v\in V$. The other points, at least
$(k+1)(N-1)+1$ of them, are joined to $v$ in at most $k+1$ colours, so one
colour $i$ occurs on at least $N$ of these pairs. Let $U$ be the set of
their other endpoints. If two points of $U$ are joined in the colour $i$,
they form a triangle of colour $i$ with $v$. Otherwise the pairs of $U$
have at most $k$ colours, and $R_k(3)\le N$ gives a monochromatic triangle
in $U$. $\square$

# 3. The centred bound

**Theorem 3.1.** Let $k,r\ge 1$ and suppose that $R_k(3)\le r$. Put
$q=\lfloor (r-1)/2\rfloor$ and $h=(k+1)q+1$. Then $[1,2h]$ is not covered by
$k+1$ sumfree sets. So
$$S(k+1)\le 2h-1=2(k+1)q+1.$$

**Proof.** Suppose that the sumfree sets $C_1,\dots,C_{k+1}$ cover
$[1,2h]$. For each $x\in[1,2h]$ choose an index $f(x)$ with
$x\in C_{f(x)}$.

1. The interval $[1,h]$ has $h=(k+1)q+1$ elements and $f$ takes at most
   $k+1$ values on it. So there is an index $i$ with $f(a)=i$ for at least
   $q+1$ elements $a\in[1,h]$. Let $A$ be the set of these elements. Then
   $A\subseteq C_i\cap[1,h]$ and $|A|\ge q+1$.
2. Let $P=\{h-a:\ a\in A\}\cup\{h+a:\ a\in A\}$. The points $h-a$ lie in
   $[0,h-1]$ and the points $h+a$ lie in $[h+1,2h]$. So
   $|P|=2|A|\ge 2q+2\ge r$, because $2q\ge r-2$.
3. Give each pair $x<y$ of points of $P$ the colour $f(y-x)$. This is
   defined, because $1\le y-x\le 2h$.
4. No pair has the colour $i$. Let $x<y$ be points of $P$ with
   $y-x\in C_i$. If $x=h-a$ and $y=h+b$ with $a,b\in A$, then $y-x=a+b$,
   and $a$, $b$, $a+b$ lie in $C_i$. If $x=h-a$ and $y=h-b$ with $a,b\in A$
   and $b<a$, then $y-x=a-b$ and $(a-b)+b=a$, with $a-b$, $b$, $a$ in
   $C_i$. If $x=h+b$ and $y=h+a$ with $b<a$, the same holds. Each case
   contradicts the fact that $C_i$ is sumfree.
5. So the pairs of $P$ have at most $k$ colours. Since $|P|\ge r$ and
   $R_k(3)\le r$, there are $x<y<z$ in $P$ and an index $j$ with
   $f(y-x)=f(z-y)=f(z-x)=j$. Then $y-x$, $z-y$ and
   $(y-x)+(z-y)=z-x$ lie in $C_j$, which contradicts the fact that $C_j$ is
   sumfree.

So $[1,2h]$ is not covered by $k+1$ sumfree sets, and
$S(k+1)\le 2h-1$. $\square$

## 3.1 Two cases

**Corollary 3.2.** $S(3)\le 13$; that is, $[1,14]$ is not covered by three
sumfree sets. Since $S(3)=13$, the bound is exact.

**Proof.** Take $k=2$ and $r=6$ in Theorem 3.1; $R_2(3)\le 6$ follows from
$R_1(3)\le 3$ by Lemma 2.5. Then $q=2$, $h=7$ and $2h=14$. $\square$

**Corollary 3.3.** Suppose that $R_4(3)\le 61$. Then $R_5(3)\le 302$ and
$S(6)\le 1801$; that is, $[1,1802]$ is not covered by six sumfree sets.

**Proof.** Lemma 2.5 with $k=4$ and $N=61$ gives
$R_5(3)\le 5\cdot 60+2=302$. Theorem 3.1 with $k=5$ and $r=302$ gives
$q=150$, $h=901$ and $2h=1802$. $\square$

## 3.2 Values of the bound

For even $r$ the bound of Theorem 3.1 is $(k+1)(r-2)+1$, and for odd $r$ it
is $(k+1)(r-1)+1$. The route through $S(k+1)\le R_{k+1}(3)-2$ and
Lemma 2.5 gives $S(k+1)\le (k+1)(r-1)$ from $R_k(3)\le r$. So Theorem 3.1
gives a bound that is smaller by $k$ when $r$ is even and larger by $1$
when $r$ is odd.

Table 1 lists the bound of Theorem 3.1 for known Ramsey bounds. Every
number in the third column comes from Theorem 3.1. The last column says
which rows are stated as Lean theorems (Section 6).

**Table 1.** The bound of Theorem 3.1.

| colours | Ramsey bound used | Theorem 3.1 gives | known value | Lean |
|:--|:-------|:-----|:-----|:------|
| 2 | $R_1(3)=3$ | $S(2)\le 5$ | $S(2)=4$ | instance not stated |
| 3 | $R_2(3)=6$ | $S(3)\le 13$ | $S(3)=13$ | Corollary 3.2 |
| 4 | $R_3(3)=17$ [GG55] | $S(4)\le 65$ | $S(4)=44$ [Bau61] | instance not stated |
| 5 | $R_4(3)\le 62$ [FKR04] | $S(5)\le 301$ | $S(5)=160$ [Heu18] | Ramsey bound not formalized |
| 6 | $R_5(3)\le 307$ [Rad26] | $S(6)\le 1837$ | open | Ramsey bound not formalized |
| 6 | $R_5(3)\le 302$, from $R_4(3)\le 61$ | $S(6)\le 1801$ | open | Corollary 3.3 |

## 3.3 Comparison for $S(6)$

The following list gives upper bounds for $S(6)$ and labels each by its
origin. Only the first item and the item for $1837$ come from this paper.

- $S(6)\le 1801$ under $R_4(3)\le 61$. This paper, Corollary 3.3, Lean
  theorem\
  `not_coveredBySumFree_Icc_six_of_triangleRamsey_four_sixtyOne`.
- $S(6)\le 1805$ under $R_4(3)\le 61$. Another method, for comparison: the
  pigeonhole recursion with the parity refinement [GG55; Rad26, Section
  6.1]. From $R_5(3)\le 302$, suppose that the edges of $K_{1807}$ have a
  colouring with six colours and no monochromatic triangle. A vertex has
  at most 301 neighbours in each colour: among 302 such neighbours there is
  an edge of that colour, or their edges have at most five colours, and
  both cases give a monochromatic triangle. Since
  each vertex has $1806=6\cdot 301$ neighbours, it has exactly 301 in each
  colour. Then each colour class is a 301-regular graph on 1807 vertices,
  which is impossible because $1807\cdot 301$ is odd. So $R_6(3)\le 1807$
  and $S(6)\le 1805$. This is not formalized.
- $S(6)\le 1806$ under $R_4(3)\le 61$. Another method, for comparison:
  Eliahou's adaptive bound [Eli20, Proposition 4], which is
  [Eli19, Proposition 2.7] in the preprint, states $R_n(3)\le n!(e-a/24)+1$
  for $n\ge 4$ when $a\le 66-R_4(3)$. With $a=5$ and $n=6$ it gives
  $R_6(3)\le 1808$, so $S(6)\le 1806$. The pigeonhole recursion without
  the parity refinement gives the same values. This is not formalized.
- $S(6)\le 1836$. Published [ER21], from $R_6(3)\le 1838$ [Rad26]; another
  method, for comparison. It uses only the published bound
  $R_4(3)\le 62$.
- $S(6)\le 1837$ from the published bound $R_5(3)\le 307$. This paper,
  Theorem 3.1 with an odd $r$; it is weaker than $1836$.

So under $R_4(3)\le 61$ the bound of Corollary 3.3 is 4 below the parity
route and 5 below the bound from [Eli20]. With the published bound
$R_4(3)\le 62$ it gives nothing new for $S(6)$.

# 4. The frontier

Let $k,t\ge 1$, suppose that $R_k(3)\le 2t+2$, and let $m=(k+1)t$.
Theorem 3.1 with $r=2t+2$ gives $q=t$ and $S(k+1)\le 2m+1$. This section
describes a Schur colouring of the frontier interval $[1,2m+1]$. The
results are necessary conditions; they do not decide whether such a
colouring exists. For example, $R_2(3)=6$ gives $t=2$, $m=6$ and the
frontier interval $[1,13]$ for three colours, which has Schur colourings
because $S(3)=13$.

## 4.1 Balanced colour classes

**Theorem 4.1.** Let $R_k(3)\le 2t+2$, let $m=(k+1)t$, and let $c$ be a
Schur colouring of $[1,2m+1]$ with $k+1$ colours. Then each colour occurs
exactly $t$ times in $[1,m]$.

**Proof.** For a colour $j$, let $D_j=\{d\in[1,m]:\ c(d)=j\}$. The points
$m-d$ and $m+d$ with $d\in D_j$ are $2|D_j|$ distinct points of $[0,2m]$,
and they lie in $\Gamma_j(m;[0,2m+1])$, because their distance to $m$ is
$d$. By Lemma 2.4 the differences of these points avoid the colour $j$, so
they have at most $k$ colours. Lemma 2.3 gives $2|D_j|<2t+2$, so
$|D_j|\le t$. The $k+1$ sets $D_j$ partition $[1,m]$, which has $(k+1)t$
elements. So $|D_j|=t$ for every $j$. $\square$

**Remark 4.2** (two centres). The reflection $x\mapsto N-x$ of $[0,N]$
keeps all distances. So, for any colouring $c$, the points $v$ and $N-v$
have the same number of neighbours of each colour in $[0,N]$. For
$N=2m+1$ this applies to the two centres $m$ and $m+1$. This remark is
proved in Lean but is not among the compared statements (Section 6).

## 4.2 The central neighbourhood and nested saturation

From here on we use $k+2$ colours and the following hypotheses.

**Frontier setting.** Let $k,u,t\ge 1$ and $m$ satisfy
$$R_k(3)\le u+1,\qquad 2t=(k+1)u,\qquad m=(k+2)t,$$
and put $N=2m+1$. Let $c$ be a Schur colouring of $[1,N]$ with $k+2$
colours, let $q=c(m+1)$, and let
$$V=\Gamma_q(m;[0,N])$$
be the *central neighbourhood*. The endpoint $N$ lies in $V$, because
$N-m=m+1$. The point $0$ lies in $V$ when $c(m)=q$.

By Lemma 2.5, $R_{k+1}(3)\le (k+1)u+2=2t+2$. So the Ramsey bound for $k$
colours, through Lemma 2.5, meets the bound for $k+1$ colours that
Theorem 4.1 needs, and $[1,N]$ is the frontier interval for $k+2$
colours. For three colours, the values $k=1$, $u=2$, $t=2$ and $m=6$
satisfy these hypotheses, with $N=13$.

**Theorem 4.3.** In the frontier setting, $|V|=2t+1$.

**Proof.** Theorem 4.1, with $k+1$ in place of $k$, applies to $c$ and
gives $t$ points $d\in[1,m]$ with $c(d)=q$. The $2t$ points $m\pm d$ for
these $d$ lie in $V\cap[0,2m]$, and $N\in V$. So $|V|\ge 2t+1$. By
Lemma 2.4 at $m$, the differences of $V$ avoid the colour $q$, so they
have at most $k+1$ colours. Lemma 2.3 with $R_{k+1}(3)\le 2t+2$ gives
$|V|<2t+2$. $\square$

**Theorem 4.4** (nested saturation). In the frontier setting, let $v\in V$.
Then $\Gamma_q(v;V)$ is empty, and $|\Gamma_i(v;V)|=u$ for every colour
$i\ne q$.

**Proof.** By Lemma 2.4 at $m$, no two points of $V$ have a difference of
colour $q$, so $\Gamma_q(v;V)$ is empty. Let $i\ne q$. The differences of
$\Gamma_i(v;V)$ avoid the colour $i$ (Lemma 2.4 at $v$) and the colour $q$
(Lemma 2.4 at $m$). So they have at most $k$ colours, and Lemma 2.3 with
$R_k(3)\le u+1$ gives $|\Gamma_i(v;V)|\le u$. The sets $\Gamma_i(v;V)$
partition $V\setminus\{v\}$, which has $2t=(k+1)u$ points by Theorem 4.3.
There are $k+1$ colours $i\ne q$, and each of their neighbourhoods has at
most $u$ points. So each has exactly $u$ points. $\square$

## 4.3 Automorphism extension

The next lemma is about an arbitrary colouring of pairs.

**Lemma 4.5.** Let $\mathrm{col}$ be a map that gives each ordered pair of
elements of a set a colour. Let $W$ be a finite subset, $e$ an element not
in $W$, and $J$ a map with $J(W)\subseteq W$, $J(J(x))=x$ and
$\mathrm{col}(J(x),J(y))=\mathrm{col}(x,y)$ for all $x,y\in W$. Let
$v\in W$, and suppose that for each colour $\gamma$ the number of
$w\in (W\cup\{e\})\setminus\{v\}$ with $\mathrm{col}(v,w)=\gamma$ is equal
to the number of $w\in (W\cup\{e\})\setminus\{J(v)\}$ with
$\mathrm{col}(J(v),w)=\gamma$. Then $\mathrm{col}(v,e)=\mathrm{col}(J(v),e)$.

**Proof.** For each colour $\gamma$, the map $J$ is a bijection from
$\{w\in W\setminus\{v\}:\ \mathrm{col}(v,w)=\gamma\}$ onto
$\{w\in W\setminus\{J(v)\}:\ \mathrm{col}(J(v),w)=\gamma\}$, with inverse
$J$. So the two counts inside $W$ are equal for each colour. Take
$\gamma=\mathrm{col}(v,e)$. The count for $v$ in $W\cup\{e\}$ is the count
in $W$ plus 1. If $\mathrm{col}(J(v),e)\ne\gamma$, the count for $J(v)$ in
$W\cup\{e\}$ is the count in $W$, which contradicts the hypothesis.
$\square$

## 4.4 Forced reflection

**Lemma 4.6.** Let $c$ be any map, $m\ge 0$, and $V=\Gamma_{c(m+1)}(m;[0,2m+1])$.
If $x\in V$ and $x\ne 2m+1$, then $2m-x\in V$ and $2m-x\ne 2m+1$.

**Proof.** Since $x\le 2m$, the point $2m-x$ lies in $[0,2m]$. It has the
same distance to $m$ as $x$, so $2m-x\ne m$ and $c(|m-(2m-x)|)=c(m+1)$.
$\square$

**Theorem 4.7** (forced reflection). In the frontier setting, let
$d\in[1,m]$ with $c(d)=q$. Then $c(m+1-d)=c(m+1+d)$.

**Proof.** Let $W=V\setminus\{N\}$, $e=N$, $J(x)=2m-x$, and
$\mathrm{col}(x,y)=c(|x-y|)$. By Lemma 4.6, $J$ maps $W$ to $W$. It is an
involution, and $|J(x)-J(y)|=|x-y|$, so it keeps the colours of all pairs
in $W$. The point $v=m+d$ lies in $W$, since $v\ne m$,
$c(|v-m|)=c(d)=q$ and $v\le 2m$; and $J(v)=m-d$. Here $W\cup\{e\}=V$. By Theorem 4.4, both $v$ and $J(v)$ have
$u$ neighbours in $V$ of each colour $i\ne q$ and none of colour $q$. So
Lemma 4.5 applies and gives $c(|m+d-N|)=c(|m-d-N|)$, that is,
$c(m+1-d)=c(m+1+d)$. $\square$

**Remark 4.8.** The reflection is not a property of every Schur colouring.
The colouring of $[1,5]$ with the colour classes $\{1,4\}$, $\{2,3\}$ and
$\{5\}$ is a Schur colouring with three colours. Take $m=2$, so that
$[1,5]=[1,2m+1]$. Then $q=c(3)$ is the colour of $\{2,3\}$, and $d=2$ has
$c(d)=q$, but $c(m+1-d)=c(1)\ne c(5)=c(m+1+d)$. In Theorem 4.7 the
reflection comes from the hypotheses of the frontier setting.

## 4.5 Paired endpoint neighbourhoods and parity

In the frontier setting, for a colour $i\ne q$ let
$$P_i=\Gamma_i(N;V)$$
be the *endpoint neighbourhood* of colour $i$.

**Theorem 4.9.** In the frontier setting, let $i\ne q$. Then:

(a) $|P_i|=u$;

(b) for every $x\in P_i$, the point $2m-x$ lies in $P_i$ and
$2m-x\ne x$;

(c) for distinct $x,y\in P_i$, the colour $c(|x-y|)$ is neither $i$ nor
$q$.

**Proof.** (a) This is Theorem 4.4 at $v=N$. (b) Let $x\in P_i$. Then
$x\in V$ and $x\ne N$, so $x\ne m$, $x\le 2m$ and $d=|m-x|$ satisfies
$1\le d\le m$ and $c(d)=q$. If $x=m-d$, then $N-x=m+1+d$ and
$N-(2m-x)=m+1-d$. If $x=m+d$, then $N-x=m+1-d$ and $N-(2m-x)=m+1+d$. In
both cases Theorem 4.7 gives $c(N-(2m-x))=c(N-x)=i$. By Lemma 4.6,
$2m-x\in V\setminus\{N\}$, so $2m-x\in P_i$. Since $x\ne m$, we have
$2m-x\ne x$. (c) The colour is not $i$ by Lemma 2.4 at $N$, and it is not
$q$ by Lemma 2.4 at $m$, because $P_i\subseteq V$. $\square$

**Corollary 4.10.** In the frontier setting, $u$ is even. So if $u$ is
odd, then no Schur colouring of $[1,2m+1]$ with $k+2$ colours exists.

**Proof.** There is a colour $i\ne q$, since $k+2\ge 2$. By Theorem 4.9,
$P_i$ lies in $[0,2m]\setminus\{m\}$, and the map $x\mapsto 2m-x$ is a
bijection from $P_i\cap[0,m-1]$ onto $P_i\cap[m+1,2m]$. So
$u=|P_i|=2\,|P_i\cap[0,m-1]|$. $\square$

## 4.6 Six colours under $R_4(3)\le 61$

**Theorem 4.11.** Suppose that $R_4(3)\le 61$. Let $c$ be a Schur colouring
of $[1,1801]$ with six colours, and let $q=c(901)$. Let $V$ be the set of
points $x\in[0,1801]$ with $x\ne 900$ and $c(|900-x|)=q$, and for a colour
$i\ne q$ let $P_i$ be the set of points $x\in V$ with $x\ne 1801$ and
$c(1801-x)=i$. Then:

(a) each colour occurs exactly 150 times in $[1,900]$;

(b) $|V|=301$, and each $v\in V$ has exactly 60 neighbours $w\in V$,
$w\ne v$, with $c(|v-w|)=i$, for each colour $i\ne q$;

(c) $c(901-d)=c(901+d)$ for every $d\in[1,900]$ with $c(d)=q$;

(d) for each colour $i\ne q$, the set $P_i$ has 60 points; it is closed
under $x\mapsto 1800-x$, and this map has no fixed point on $P_i$; and for
distinct $x,y\in P_i$ the colour $c(|x-y|)$ is neither $i$ nor $q$.

**Proof.** The frontier setting holds with $k=4$, $u=60$, $t=150$ and
$m=900$: $R_4(3)\le 61=u+1$, $2t=300=5\cdot 60$, $m=6\cdot 150$ and
$N=1801$. Part (a) is Theorem 4.1 with $R_5(3)\le 302$ (Corollary 3.3).
Part (b) is Theorems 4.3 and 4.4, part (c) is Theorem 4.7, and part (d)
is Theorem 4.9. $\square$

By part (d), each $P_i$ is the union of 30 pairs $\{900-d,900+d\}$ with
$c(d)=q$. The difference colouring on $P_i$ is a colouring of the edges of
a complete graph on 60 vertices with at most four colours and no
monochromatic triangle (Lemma 2.2), and the map $x\mapsto 1800-x$ is an
involution of $P_i$ without fixed point that keeps the colours of all
edges. So, under $R_4(3)\le 61$, a Schur colouring of $[1,1801]$ with six
colours gives five such structures, one for each colour $i\ne q$.

**Remark 4.12.** Let $c$ be a Schur colouring of $[1,1801]$ with six
colours, and suppose that $R_4(3)\le 61$. Then $R_4(3)=61$. Indeed, let
$q=c(901)$ and take a colour $i\ne q$. The 60 points of $P_i$ lie in $[0,1800]$, and by
Theorem 4.11 (d) and Lemma 2.2 the difference colouring on $P_i$ is a
colouring of the edges of $K_{60}$ with at most four colours and no
monochromatic triangle. So $R_4(3)\ge 61$. This remark is not formalized.

These results do not prove $S(6)\le 1800$, even under $R_4(3)\le 61$. They
give necessary conditions for the existence of a Schur colouring of
$[1,1801]$ with six colours, and we do not show that they cannot be met. Since
$u=60$ is even, Corollary 4.10 does not apply. Whether the five 60-point
structures of Theorem 4.11 exist is open.

# 5. Literature

We checked the following sources, first in a local library of papers and
then on the web, in September and October 2026. We looked for
Theorem 3.1, the argument of its proof, an upper bound for $S(6)$ below
1836, and a consequence of $R_4(3)\le 61$ for the Schur numbers.

- Eliahou and Revuelta, both the preprint [ER20] and the refereed version
  [ER21]. Both give $S(6)\le R_6(3)-2\le 1836$ as the best known upper
  bound, and both say that, as far as theory is concerned, nothing better
  than $S(4)\le R_4(3)-2\le 60$ is known.
- Eliahou, both the preprint [Eli19] and the refereed version [Eli20]. The
  bound $1806$ of Section 3.3 comes from [Eli20, Proposition 4], which is
  [Eli19, Proposition 2.7].
- Heule [Heu18]; Irving [Irv73]; Radziszowski [Rad26]; Hegde, Lott,
  Petridis and Ponagandla [HLPP26]; Abbott and Hanson [AH72], in a scan
  with poor text recognition.
- Adhikari, Boza, Eliahou, Marín, Revuelta and Sanz [ABEMRS15]. It cites
  the Schur bound of [Wan97] in one sentence (Section 1.1), with no method.
  In the proof of its Corollary 5.7 it uses $S_2(5)\le 306$, that is,
  $S(5)\le 305$.
- Eliahou and Fares [EF16]. It cites [Wan97] only for the bound on
  $R_n(3)$.
- Myers [Mye15], a PhD thesis. It cites [Wan97] once, only for the
  constant of the bound on $R_n(3)$, and it does not mention the Schur
  bound of [Wan97].
- Kościuszko [Kos25]. For another equation, it splits a colour
  neighbourhood of a vertex $v$ into the parts $v+A$ and $v-A$. It uses the
  larger part only in a lower bound for the independence number, and it
  takes a largest independent set as the next set. It uses no centre point
  and no parity step.
- The repository [Tat26], all its Markdown files at the commit cited. They
  do not mention Schur numbers. We found no preprint or other announcement
  of $R_4(3)\le 61$ on arXiv, Hacker News, MathOverflow, Mathematics Stack
  Exchange, Tatarevic's blog or in the OEIS entry A003323. We could not
  search X, Reddit, Bluesky or Mastodon.

None of the sources that we read states Theorem 3.1, its argument, an
upper bound for $S(6)$ below 1836, or a consequence of $R_4(3)\le 61$ for
the Schur numbers.

From the published even bound $R_4(3)\le 62$, Theorem 3.1 gives
$S(5)\le 301$ (Table 1). [ER21, Section 5.2] calls $S(5)\le 305$ "the
currently best known theoretical upper bound", and [ABEMRS15] uses the
same value 305. The bound of [Wan97] on $S_n$ that is discussed below is
stated only for even $n\ge 6$.

Two sources may contain the argument of Theorem 3.1 or a similar
argument, and we did not read either of them in full. By its zbMATH
summary (Zbl 0882.05095), Wan [Wan97] proves
$R_n(3)<n!\,(e-e^{-1}+3)/2+1$ for $n\ge 4$, which [Eli20] also cites, and
$S_n<n!\,(e-e^{-1}+3)/2-n+2$ for even $n\ge 6$. We could not obtain the
full text of [Wan97], so we do not know its argument. The summary does not
define $S_n$. Two conventions are in use [Heu18, footnote 1]: $S_n$ is the
largest $N$ such that $[1,N]$ has a Schur colouring with $n$ colours, which
is our $S(n)$, or the least $N$ such that every colouring of $[1,N]$ with
$n$ colours has a monochromatic solution of $x+y=z$, which is $S(n)+1$.
Adhikari et al. [ABEMRS15] use the second convention and write $S_2(n)$.
From Wan's bound $R_5(3)\le 322$, the route through Lemma 2.5 gives
$S(6)\le 1926$, and Theorem 3.1 gives $S(6)\le 1921$.

- If Wan's $S_n$ is our $S(n)$, the summary gives $S(6)\le 1922$, which is
  1 above the value 1921 that Theorem 3.1 gives from Wan's own bound
  $R_5(3)\le 322$.
- If Wan's $S_n$ is $S(n)+1$, the summary gives $S(6)\le 1921$, the same
  value. Under this reading the two bounds agree for every even $n$ from 6
  to 30: put $r=\lfloor (n-1)!\,(e-e^{-1}+3)/2\rfloor+1$, which is Wan's
  bound on $R_{n-1}(3)$ and is even for these $n$; then
  $\lfloor n!\,(e-e^{-1}+3)/2\rfloor-n+2-1=2n\lfloor (r-1)/2\rfloor+1$.
  We computed both sides in exact rational arithmetic.

So Wan's bound for even $n$ may come from the argument of Theorem 3.1, or
from an argument of the same strength. We have not read his proof. The
method of Theorem 3.1 is probably not new.

By its abstract, Li Huai'en [Li92] proves
$R_n(3)\le n!\,(3/2+\sinh 1)+1$, where $3/2+\sinh 1=(e-e^{-1}+3)/2$, with
the pigeonhole principle and parity arguments, and also improves upper
bounds for the Schur numbers. We read only its abstract.

We did not read Whitehead [Whi73]; Xu, Xie and Chen [XXC02], whose title
names upper bounds for $R_n(3)$ and for the Schur numbers; Fredricksen
[Fre79]; Landman and Robertson [LR14]; or Soifer [Soi24]. In October 2026
OpenAlex listed 24 works that cite [Wan97]; apart from the sources listed
above, we did not go through them. This list of unread sources is not
complete.

We make no claim of novelty for Theorem 3.1 or for its method.

# 6. Lean formalization

The theorems of Sections 2 to 4 are formalized in Lean 4 [MU21] with
Mathlib [mC20], with the Lean toolchain v4.35.0-rc3 and the Mathlib tag
v4.35.0-rc3. The library `ClassicalSchur` has four modules:

- `Basic`: sumfree sets (`SumFree`) and covers by sumfree sets
  (`CoveredBySumFree`);
- `Ramsey`: the statement `TriangleRamsey k N`, which is $R_k(3)\le N$,
  and the pigeonhole bound $\rho(k)$ with $\rho(0)=2$ and
  $\rho(k+1)=(k+1)(\rho(k)-1)+2$;
- `SchurBound`: Lemma 2.5, Theorem 3.1 and Corollaries 3.2 and 3.3;
- `Frontier`: Schur colourings, colour neighbourhoods, Lemmas 2.1 to 2.4,
  and Section 4.

The file `Challenge.lean` imports only Mathlib. It states seven
definitions (`SumFree`, `CoveredBySumFree`, `TriangleRamsey`,
`SchurColoring`, `colorNbhd`, `centralNbhd`, `endpointNbhd`) and fourteen
theorems, with the proofs left as `sorry`. The file `Solution.lean` imports
the library, which proves the fourteen theorems under the same names. The
file `comparator.json` lists the fourteen theorems and permits only the
axioms `propext`, `Classical.choice` and `Quot.sound`. The script
`scripts/verify-comparator.sh` runs `lake comparator` [LFRO], which is
part of Lake in the Lean toolchain, on these three files: it compares each
statement in `Solution.lean`, with the definitions that it uses, against
`Challenge.lean`, and checks the axioms. The repository's continuous
integration runs this script. The fourteen theorems use no axioms other
than `propext`, `Classical.choice` and `Quot.sound`.

The hypothesis $R_4(3)\le 61$ enters only as the explicit argument
`TriangleRamsey 4 61` of two theorems:

- `not_coveredBySumFree_Icc_six_of_triangleRamsey_four_sixtyOne`
  (Corollary 3.3);
- `schur_six_frontier_structure` (Theorem 4.11).

The library does not prove $R_4(3)\le 61$ and does not import [Tat26]. The Lean development of [Tat26] uses its own definitions
and Lean v4.32.1, and this repository does not join the two developments
in one build.

The results correspond to Lean declarations in the namespace
`ClassicalSchur` as follows. The declarations marked $*$ are among the
fourteen compared theorems.

**Table 2.** Results and Lean declarations.

| Result | Lean declaration |
|:--|:---------------|
| Lemma 2.1 (a) | `coveredBySumFree_of_schurColoring` $*$ |
| Lemma 2.1 (b) | `exists_schurColoring_of_coveredBySumFree` $*$ |
| Lemma 2.2 | `SchurColoring.not_mono` |
| Lemma 2.3 | `SchurColoring.card_lt` |
| Lemma 2.4 | `SchurColoring.color_ne_of_mem_colorNbhd` |
| Lemma 2.5 | `triangleRamsey_succ` $*$ |
| Theorem 3.1 | `not_coveredBySumFree_Icc_of_triangleRamsey` $*$ |
| Corollary 3.2 | `not_coveredBySumFree_Icc_fourteen_three` $*$ |
| Corollary 3.3 | `not_coveredBySumFree_Icc_six_of_triangleRamsey_four_sixtyOne` $*$ |
| Theorem 4.1 | `card_filter_Icc_eq_of_frontier` $*$ |
| Remark 4.2 | `card_colorNbhd_range_reflect`, `card_colorNbhd_two_centres` |
| Theorem 4.3 | `card_centralNbhd_of_frontier` $*$ |
| Theorem 4.4 | `card_colorNbhd_centralNbhd_of_frontier` $*$, `SchurColoring.color_ne_of_mem_centralNbhd` |
| Lemma 4.5 | `color_eq_of_card_filter_eq` $*$ |
| Lemma 4.6 | `reflect_mem_centralNbhd` |
| Theorem 4.7 | `color_reflect_of_frontier` $*$ |
| Theorem 4.9 | `endpointNbhd_of_frontier` $*$ |
| Corollary 4.10 | `even_of_frontier` $*$, `not_schurColoring_frontier_of_odd` |
| Theorem 4.11 | `schur_six_frontier_structure` $*$ |

In Corollary 3.3 the bound $R_5(3)\le 302$ is the case $k=4$, $N=61$ of
`triangleRamsey_succ`. In Corollary 3.2 the bound $R_2(3)\le 6$ is proved
in Lean through $\rho(2)=6$. The following are not formalized: the rows of
Table 1 other than Corollaries 3.2 and 3.3, the bounds $1805$, $1806$ and
$1836$ of Section 3.3, Remarks 4.8 and 4.12, the numbers of Section 5, and the
Ramsey bounds $R_4(3)\le 62$, $R_4(3)\le 61$ and $R_5(3)\le 307$.

The Lean statements differ from the prose in the following ways.

- The ambient type is $\mathbb{N}$. All sets are sets of natural numbers,
  and $[1,N]$ is `Set.Icc 1 N`. Subtraction and division are those of
  $\mathbb{N}$; for example, Theorem 3.1 is stated for
  `Set.Icc 1 (2 * ((k + 1) * ((r - 1) / 2) + 1))`, for all natural $k$
  and $r$.
- A colouring with $n$ colours takes values in `Fin n`. In
  `TriangleRamsey k N` the vertices are natural numbers in a finite set of
  at least $N$ elements, only the pairs $x<y$ are coloured, and the colours
  are natural numbers from a set of at most $k$ elements.
- $S(n)$ is not defined in Lean. Each bound $S(n)\le M$ is stated as
  `¬ CoveredBySumFree (Set.Icc 1 (M + 1)) n`.
- A Schur colouring is a map from $\mathbb{N}$ to `Fin n`, defined on all
  of $\mathbb{N}$. Only its values on $[1,N]$ are constrained.
- The distance $|x-y|$ is `Nat.dist x y`.
- Neighbourhoods are `Finset`s. The central neighbourhood `centralNbhd c m`
  is the colour-$c(m+1)$ neighbourhood of $m$ in
  $\{0,1,\dots,2m+1\}$, and `endpointNbhd c m i` is the colour-$i$
  neighbourhood of $2m+1$ in it.
- Lemma 2.1 says that the colour classes of a Schur colouring are sumfree
  sets that cover $[1,N]$, and that a map that picks an index of a
  covering set is a Schur colouring. The Lean theorems
  `coveredBySumFree_of_schurColoring` and
  `exists_schurColoring_of_coveredBySumFree` state only that a cover by $n$
  sumfree sets, or a Schur colouring with $n$ colours, exists.
- Theorem 4.4 has two parts. The compared theorem
  `card_colorNbhd_centralNbhd_of_frontier` states only
  $|\Gamma_i(v;V)|=u$ for $i\ne q$. That $\Gamma_q(v;V)$ is empty follows
  from `SchurColoring.color_ne_of_mem_centralNbhd` (no two distinct points
  of $V$ have a difference of colour $q$), which the library proves but
  which is not among the compared theorems.
- `color_eq_of_card_filter_eq` (Lemma 4.5) is stated for any types with
  decidable equality and a colouring of ordered pairs.
- The frontier theorems take the hypotheses $2t=(k+1)u$ and $m=(k+2)t$ as
  equations of natural numbers, with colours in `Fin (k + 2)`. They hold
  in Lean for all natural numbers $k$, $u$ and $t$, while the prose has
  $k,u,t\ge 1$. The added cases are vacuous: for $u=0$ the hypothesis
  `TriangleRamsey k 1` is false (take a single point), and for $k=0$ and
  $u\ge 1$ the hypotheses give $t\ge 1$ and $m=2t$, and $[1,2m+1]$ has no
  Schur colouring with two colours, since $S(2)=4$.

**Data and code availability.** The Lean source, `Challenge.lean`,
`Solution.lean` and `comparator.json` are in the repository that contains
this paper.

# Acknowledgements and use of AI tools

The argument of Theorem 3.1 was first written by an AI agent based on
ChatGPT (OpenAI) in a project discussion on 27 September 2026. A Claude
agent (Anthropic) audited it: it rebuilt each step, and it checked
$S(2)=4$ and the absence of a Schur colouring of $[1,14]$ with three
colours by exhaustive search. Claude (model Claude Opus 5.5) wrote the
Lean proof, under the direction of the author. The argument of Section 4
(balanced colour classes, saturation, reflection, and the paired endpoint
neighbourhoods with the parity of $u$) was proposed by an AI agent based on
ChatGPT (OpenAI) in a project discussion on 2 October 2026. Claude checked
each step, restated it with explicit hypotheses, and wrote the Lean proofs.
The Lean kernel checks every proof. On 2 October 2026 an independent
Claude agent rebuilt the Lean module of Section 4, ran its axiom audit
again, and checked its statements and each step against the argument,
including the example with $S(3)=13$. On 3 October 2026 another
independent Claude agent checked all fourteen compared statements and all
proofs of Sections 2 to 4 of this paper against the Lean, and recomputed
the numbers. The comparison of `Challenge.lean` with `Solution.lean` (the
types and values of the seven definitions and the types of the fourteen
theorems) was done by the Claude session that wrote the repository, not
by a separate agent; the comparator run in continuous integration is the
formal check of it. The text of this paper was written with Claude
under the direction of the author. The author has checked the content and
takes responsibility for it.

# References

- [ABEMRS15] S. D. Adhikari, L. Boza, S. Eliahou, J. M. Marín,
  M. P. Revuelta, M. I. Sanz, On the $n$-color Rado number for the equation
  $x_1+x_2+\dots+x_k+c=x_{k+1}$, Math. Comp. 85(300), 2047–2064,
  electronically published 14 September 2015. doi:10.1090/mcom3034.
- [AH72] H. L. Abbott, D. Hanson, A problem of Schur and its
  generalizations, Acta Arith. 20(2) (1972), 175–187.
  doi:10.4064/aa-20-2-175-187.
- [Bau61] L. D. Baumert, Sum-free sets, J.P.L. Research Summary No. 36-10
  (1961), 16–18.
- [Chk26] A. McKenna, Independent LRAT certificate check of all 56,830 SAT
  formulas, issue 1 of the repository milostatarevic/r3333-upper-bound,
  posted from the GitHub account flound1129, 2 October 2026.
  <https://github.com/milostatarevic/r3333-upper-bound/issues/1>.
- [Chu73] F. R. K. Chung, On the Ramsey numbers $N(3,3,\dots,3;2)$,
  Discrete Math. 5 (1973), 317–321.
- [EF16] S. Eliahou, Y. Fares, Poonen's conjecture and Ramsey numbers,
  Discrete Appl. Math. 209 (2016), 102–106.
  doi:10.1016/j.dam.2015.07.038.
- [Eli19] S. Eliahou, An adaptive upper bound on the Ramsey numbers
  $R(3,\dots,3)$, preprint, arXiv:1912.05353v1 (2019).
- [Eli20] S. Eliahou, An adaptive upper bound on the Ramsey numbers
  $R(3,\dots,3)$, Integers 20 (2020), Paper No. A54.
- [ER20] S. Eliahou, M. P. Revuelta, The Schur degree of additive sets,
  preprint, arXiv:2006.01502v1 (2020).
- [ER21] S. Eliahou, M. P. Revuelta, The Schur degree of additive sets,
  Discrete Math. 344(5) (2021), Article 112332.
  doi:10.1016/j.disc.2021.112332.
- [Exo94] G. Exoo, A lower bound for Schur numbers and multicolor Ramsey
  numbers of $K_3$, Electron. J. Combin. 1 (1994), #R8.
  doi:10.37236/1188.
- [FKR04] S. E. Fettes, R. L. Kramer, S. P. Radziszowski, An upper bound of
  62 on the classical Ramsey number $R(3,3,3,3)$, Ars Combin. 72 (2004),
  41–63.
- [Fre79] H. Fredricksen, Schur numbers and the Ramsey numbers
  $N(3,3,\dots,3;2)$, J. Combin. Theory Ser. A 27(3) (1979), 376–377.
  doi:10.1016/0097-3165(79)90028-1.
- [FS00] H. Fredricksen, M. M. Sweet, Symmetric sum-free partitions and
  lower bounds for Schur numbers, Electron. J. Combin. 7 (2000), #R32.
  doi:10.37236/1510.
- [GG55] R. E. Greenwood, A. M. Gleason, Combinatorial relations and
  chromatic graphs, Canad. J. Math. 7 (1955), 1–7.
  doi:10.4153/CJM-1955-001-4.
- [Heu18] M. J. H. Heule, Schur number five, in: Proceedings of the AAAI
  Conference on Artificial Intelligence 32(1) (AAAI-18) (2018), 6598–6606.
  doi:10.1609/aaai.v32i1.12209. Preprint arXiv:1711.08076v1 (2017).
- [HLPP26] S. Hegde, A. Lott, G. Petridis, N. R. Ponagandla, Refined upper
  bounds on Schur-like numbers, preprint, arXiv:2608.03661v1 (2026).
- [Irv73] R. W. Irving, An extension of Schur's theorem on sum-free
  partitions, Acta Arith. 25(1) (1973), 55–64.
  doi:10.4064/aa-25-1-55-64.
- [Kos25] T. Kościuszko, Schur-like numbers and a lemma of Shearer,
  preprint, arXiv:2507.21656v1 (2025).
- [LFRO] Lean FRO, `lake comparator`, in Lake, Lean 4 toolchain
  v4.35.0-rc3, software. <https://github.com/leanprover/lean4>.
- [Li92] Li Huai'en, On upper bounds for the Ramsey numbers $r_n$ and the
  Schur numbers $s_n$ (in Chinese; title translated), J. Zhengzhou Univ.
  (Sci.) 1992, no. 4, 20–25.
- [LR14] B. Landman, A. Robertson, Ramsey Theory on the Integers, 2nd ed.,
  Student Mathematical Library 73, American Mathematical Society (2014).
  doi:10.1090/stml/073.
- [mC20] The mathlib Community, The Lean mathematical library, in:
  Proceedings of the 9th ACM SIGPLAN International Conference on Certified
  Programs and Proofs (CPP 2020), ACM (2020), 367–381.
  doi:10.1145/3372885.3373824.
- [MU21] L. de Moura, S. Ullrich, The Lean 4 theorem prover and programming
  language, in: Automated Deduction – CADE 28, Lecture Notes in Comput.
  Sci. 12699, Springer (2021), 625–635. doi:10.1007/978-3-030-79876-5_37.
- [Mye15] K. J. Myers, Computational Advances in Rado Numbers, PhD thesis,
  Rutgers, The State University of New Jersey (2015).
  doi:10.7282/t3gh9ktt.
- [Rad26] S. P. Radziszowski, Small Ramsey numbers, Electron. J. Combin.,
  Dynamic Survey DS1, revision 18 (2026). doi:10.37236/21.
- [Sch16] I. Schur, Über die Kongruenz $x^m+y^m\equiv z^m \pmod p$,
  Jahresber. Dtsch. Math.-Ver. 25 (1916), 114–117.
- [Soi24] A. Soifer, The New Mathematical Coloring Book: Mathematics of
  Coloring and the Colorful Life of Its Creators, Springer (2024).
  doi:10.1007/978-1-0716-3597-1.
- [Tat26] M. Tatarevic, An improved upper bound for the Ramsey number
  $R(3,3,3,3)$, repository, commit
  ddd7755476db3f0751181db0daec75342576cdd1 (24 September 2026).
  <https://github.com/milostatarevic/r3333-upper-bound>.
- [Wan97] H. Wan, Upper bounds for Ramsey numbers $R(3,3,\dots,3)$ and
  Schur numbers, J. Graph Theory 26(3) (1997), 119–122.
  doi:10.1002/(SICI)1097-0118(199711)26:3\<119::AID-JGT1\>3.0.CO;2-U.
- [Whi73] E. G. Whitehead Jr., The Ramsey number $N(3,3,3,3;2)$, Discrete
  Math. 4(4) (1973), 389–396. doi:10.1016/0012-365X(73)90174-X.
- [XXC02] X. Xu, Z. Xie, Z. Chen, Upper bounds for Ramsey numbers $R_n(3)$
  and Schur numbers (in Chinese), Math. Econ. 19(1) (2002), 81–84.
