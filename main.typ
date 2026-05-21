#import "typst/packages/preview/mousse-notes/1.1.0/src/lib.typ": *
#import "@preview/xarrow:0.3.1": xarrow
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#let smallcaps-strong = it => smallcaps(strong(it))
#let claim = thm-env("Claim", fmt: smallcaps-strong, body-fmt: emph)

#let member(..args) = edge(..args, " ", label: $in$, label-side: center, label-angle: right)

// override default numbering-internal for theorem-like environments
#let theorem = theorem.with(numbering-internal: "(i)")
#let proposition = proposition.with(numbering-internal: "(i)")
#let lemma = lemma.with(numbering-internal: "(i)")
#let corollary = corollary.with(numbering-internal: "(i)")
#let definition = definition.with(numbering-internal: "(i)")
#let example = example.with(numbering-internal: "(i)")
#let remark = remark.with(numbering-internal: "(i)")
#let claim = thm-env("Claim", fmt: smallcaps-strong, body-fmt: emph).with(numbering-internal: "(i)")

#set page(paper: "us-letter")
#show: book.with(
  title: [Riemann Surface],
  subtitle: [Lecture Notes],
  author: "Poshen Chang",
  font-style: "serif",
)

#set enum(numbering: "(i)")

#let varinjlim = math.accent(math.lim, sym.arrow.r.long)
#let iff = math.arrow.l.r.double.long

#outline(indent: auto)
#pagebreak()

= Covering Spaces

== Preliminaries

#definition[
    Let $X$ be a Hausdorff topological space. $X$ is called a $2$-dimensional topological manifold if for every $x in X$, there exists an open neighborhood $U$ of $x$ such that $U$ is homeomorphic to an open subset of $RR^2$.
]

#definition[
    Let $X$ be a $2$-dimensional topological manifold. A chart of $X$ is a homeomorphism $phi.alt: U-> V$ where $U$ is an open subset of $X$ and $V$ is an open subset of $CC$. A complex atlas of $X$ is a collection of charts $\{phi.alt_j: U_j-> V_j\}_(j in I)$ such that $\{U_j\}_(j in I)$ is an open cover of $X$ and for every $j,k in I$ with $U_j inter U_k!= emptyset$, the composition $phi.alt_k compose phi.alt_j^(-1): phi.alt_j (U_j inter U_k)-> phi.alt_k (U_j inter U_k)$ is biholomorphic. Two complex atlases $\{phi.alt_j\}_(j in I)$ and $\{psi_alpha\}_(alpha in A)$ are said to be equivalent if their union is also a complex atlas. A complex structure on $X$ is an equivalence class of complex atlases. A Riemann surface is a *connected $2$-dimensional topological manifold* equipped with a *complex structure*.
]

#definition[
    Let $X$ be a Riemann surface. A function $f: X-> CC$ is holomorphic if $f compose phi.alt_j^(-1): V_j-> CC$ is holomorphic for every chart $phi.alt_j: U_j-> V_j$ of $X$.
]

#remark[
    On Riemann surfaces, we often write $(U, z)$ locally instead of $phi.alt: U-> V$ to denote a chart, where $z$ is the local coordinate on $U$.
]

#definition[
    Let $X$ be a Riemann surface. For a open subset $Y subset X$, the restriction of the complex structure on $X$ to $Y$ gives a complex structure on $Y$. Let $cal(O)(Y)$ denote the $CC$-algebra of holomorphic functions on $Y$.
]

#theorem(name: "Riemann's removable singularity theorem")[ 
    Let $X$ be a Riemann surface and $U subset X$ be an open subset. If $a in U$ and $f in cal(O)(U without \{a\})$ is bounded in a neighborhood of $a$, then $f$ can be extended uniquely to $tilde(f) in cal(O)(U)$.
]
#proof[
    Let $phi.alt$ be a chart at $a$, then since $f$ is bounded in a neighborhood of $a$, we have
    $
    lim_(z-> phi.alt(a)) (z-phi.alt(a))f compose phi.alt^(-1)(z) = 0.
    $
    Apply Riemann's removable singularity theorem in complex analysis, we can extend $f compose phi.alt^(-1)$ to a holomorphic function $g$ on $phi.alt(U)$, and then define $tilde(f) = g compose phi.alt$. The uniqueness of $tilde(f)$ follows from the identity theorem for holomorphic functions.
$qed$
]

#definition[
    A meromorphic function on $Y subset X$ if there exists $Y' subset Y$ such that
    + $f in cal(O)(Y')$;
    + $Y without Y'$ is a discrete subset of $Y$;
    + for every $a in Y without Y'$,
    $
    lim_(x-> a) |f(x)| = oo.
    $
    The set of meromorphic functions on $Y$ is denoted by $cal(M)(Y)$.
]

#definition[
    Let $X$ and $Y$ be Riemann surfaces. A holomorphic map from $X$ to $Y$ is a continuous map $f: X-> Y$ such that for every chart $phi.alt: U-> V$ of $X$ and every chart $psi: U'-> V'$ of $Y$ with $f(U) subset U'$, the composition $psi compose f compose phi.alt^(-1): V-> V'$ is holomorphic. A biholomorphism is a holomorphic map that has a holomorphic inverse.
]

#remark[
    A holomorphic map $f: X-> Y$ induces a pullback map $f^*: cal(O)(Y)-> cal(O)(X)$ defined by $f^*(g) = g compose f$ for every $g in cal(O)(Y)$.
]

#theorem(name: "Identity theorem")[ 
    Let $X$ be a Riemann surface and $f,g in cal(O)(X)$. If $f$ and $g$ agree on a subset of $A subset X$ that has an accumulation point, then $f equiv g$ on $X$.
    
]
#proof[
    Let
    $
    G = \{x in X: exists " a neighborhood " W " of " x " such that " f|_W = g|_W\}.
    $
    Then $G$ is open. Let $b in overline G$, then $f(b) = g(b)$ by the continuity of $f$ and $g$. Choose connected neighborhoods $U$ of $b$ and $V$ of $f(b)$ such that there exist charts $phi.alt: U-> phi.alt(U)$ and $psi: V-> psi(V)$. Then $psi compose f compose phi.alt^(-1)$ and $psi compose g compose phi.alt^(-1)$ are holomorphic functions on $phi.alt(U)$ that agree on a subset of $phi.alt(U)$ that has an accumulation point. By the identity theorem for holomorphic functions, we have $psi compose f compose phi.alt^(-1) = psi compose g compose phi.alt^(-1)$ on $phi.alt(U)$, which implies $f|_U = g|_U$. Hence $b in G$, which shows that $G$ is closed.

    By our assumption, $A$ has an accumulation point $a$, by a similar argument as above, we can show that $a in G$. Since $G$ is nonempty, open and closed, we have $G = X$, which implies $f equiv g$ on $X$.
    $qed$
]

#definition[
    Let $tilde(C) = CC union \{oo\}$ be the one point compactification of $CC$. The Riemann sphere $PP^1$ is the complex structure on $tilde(C)$ given by the charts $\{phi.alt_1: CC-> CC, z|-> z\}$ and $\{phi.alt_2: tilde(C) without \{0\}-> CC, z|-> 1/z\}$.
]

#theorem[
    Let $X$ be a Riemann surface and $f in cal(M)(X)$. For each pole $x$ of $f$, define $f(x) = oo$. Then $f$ can be viewed as a holomorphic map from $X$ to $PP^1$. Conversely, every holomorphic map from $X$ to $PP^1$ is either identically $oo$ or a meromorphic function on $X$.
    
]
#proof[
    The extended map $f: X-> PP^1$ is clearly continuous. For every chart $phi.alt: U-> V$ of $X$ and every chart $psi: U'-> V'$ of $PP^1$ with $f(U) subset U'$, the composition $psi compose f compose phi.alt^(-1): V-> V'$ is holomorphic since it is either a holomorphic function on $V$ or a holomorphic function on $V without \{phi.alt(x)\}$ that has a pole at $phi.alt(x)$, which can be extended to a holomorphic function on $V$ by Riemann's removable singularity theorem. Hence $f$ is a holomorphic map from $X$ to $PP^1$.

    Conversely, let $f: X-> PP^1$ be a holomorphic map. If $f equiv.not oo$, then the set of poles of $f$ is discrete, impling that $f$ is a meromorphic function on $X$.
    $qed$
]

From the above theorem, we can conclude that meromorphic functions also satisfy the identity theorem, hence if $f equiv.not 0$, then $f^(-1)(0)$ is a discrete subset of $X$. This implies that $cal(M)(X)$ is in fact a field.

Under the local coordinate $z$ of a chart $(U, z)$ such that $z(p) = 0$ for some pole $p$, then we can write a meromorphic function $f$ on $U$ as a Laurent series
$
f = sum_(n=m)^(oo) a_n z^n.
$
If $m < 0$, then $f$ has a pole of order $-m$ at $p$. If $m >= 0$, then $f$ is holomorphic at $p$. If $m > 0$, then $f$ has a zero of order $m$ at $p$.

#theorem[
    Let $X, Y$ be Riemann surfaces and $f: X-> Y$ be a non-constant holomorphic map. Suppose $a in X$ and $b = f(a)$. Then there exist charts $(U, z)$ at $a$ and $(V, w)$ at $b$ such that $f(U) subset V$ and
    $
    w compose f compose z^(-1)(zeta) = zeta^k
    $
    for some positive integer $k$.
    
]
#proof[
    Pick charts $(U, z)$ at $a$ and $(V, w)$ at $b$ such that $f(U) subset V$, $z(a) = 0$, and $w(b) = 0$. Then $w compose f compose z^(-1)$ is a holomorphic map from a neighborhood of $0$ in $CC$ to a neighborhood of $0$ in $CC$. Since $f$ is non-constant, we can write $f_1 := w compose f compose z^(-1) = z^k g$ for some positive integer $k$ and some holomorphic function $g$ with $g(0)!= 0$. By shrinking $U$ if necessary, we can assume that $g(zeta)!= 0$ for every $zeta in z(U)$. Then we can take a holomorphic $k$-th root of $g$, denoted by $h$. Replacing $z$ by $h dot z$, we get the desired property
    $
    w compose f compose z^(-1)(zeta) = (z dot h(zeta))^k => w compose f compose (z dot h)^(-1)(zeta) = zeta^k.
    $
    $qed$
]

#lemma[
    Non-constant holomorphic maps are open maps.
]

#lemma(name: "Maximal Principle")[ 
    Suppose $X$ is a Riemann surface and $f: X-> CC$ is a non-constant holomorphic function. Then $|f|$ does not attain its maximum on $X$.
    
]
#proof[
    If not, say $R = |f(a)| = sup_(x in X) |f(x)|$ for some $a in X$. Then $f(X) subset overline(B_R (0))$. Since $f$ is an open map, $f(X)$ contains an open neighborhood of $f(a)$, which contradicts the definition of $R$.
    $qed$
]

#theorem[
    Suppose $X, Y$ are Riemann surfaces. Suppose $X$ is compact and $f: X -> Y$ is a holomorphic map. Then $Y$ is compact and $f$ is surjective.
    
]
#proof[
    Since $X$ is compact, $f(X)$ is compact, in particular closed. Since $f$ is an open map, $f(X)$ is also open. Hence $f(X) = Y$, which implies that $Y$ is compact and $f$ is surjective.
    $qed$
]

#lemma[
    Every holomorphic function on a compact Riemann surface is constant.
    
]
#proof[
    This follows from the previous theorem since $CC$ is not compact.
    $qed$
]

#example[
    Let $omega_1, omega_2$ be linearly independent complex numbers. Define a lattice $Gamma = ZZ omega_1 + ZZ omega_2$ and the equivalence relation $tilde.op$ on $CC$ by $z tilde.op w$ if and only if $z-w in Gamma$. Consider the quotient space $X = CC\/Gamma = CC\/tilde.op$ with the quotient topology, that is, the topology given by
    $
    \{ U subset.eq CC\/Gamma : pi^(-1) (U) " is open in " CC \},
    $
    where $pi: CC-> CC\/Gamma$ is the projection map. Let $V subset CC$ be an open set such that no two points in $V$ are equivalent under $tilde.op$. Then $pi|_V: V-> pi(V)$ is a homeomorphism, whose inverse $phi.alt: pi(V)-> V$ is a chart of $X$. The collection of charts $\{phi.alt: pi(V)-> V\}$ gives a complex structure on $X$, which makes $X$ a Riemann surface.
]

== The Fundamental Group

#definition[
    Let $X$ be a topological space and $a, b in X$. A curve from $a$ to $b$ is a continuous map $u: I-> X$ such that $u(0) = a$ and $u(1) = b$, where $I = [0, 1]$. Two curves $u, v$ from $a$ to $b$ are homotopic, denoted by $u tilde.op v$, if there exists a continuous map $A: I times I-> X$ such that
    
    + $A(t, 0) = u(t)$ for every $t in I$;
    + $A(t, 1) = v(t)$ for every $t in I$;
    + $A(0, s) = a, A(1, s) = b$ for every $s in I$.
    
]

#theorem[
    The homotopy relation $tilde.op$ is an equivalence relation on the set of curves from $a$ to $b$.
    
]
#proof[
    The reflexivity and symmetry of $tilde.op$ are clear. To show the transitivity, let $u, v, w$ be curves from $a$ to $b$ such that $u limits(tilde.op)^A v$ and $v limits(tilde.op)^B w$. Define a continuous map $C: I times I-> X$ by
    $
    C(t, s) = cases(
        A(t, 2s) "if " 0<= s <= 1/2 ,
        B(t, 2s-1) "if " 1/2 < s <= 1,
    )
    $
    Then $C$ is a homotopy from $u$ to $w$, which shows that $u tilde.op w$.
    $qed$
]

#definition[
    Let $u$ be a curve from $a$ to $b$ and $v$ be a curve from $b$ to $c$. Define the product of $u$ and $v$ to be the curve $u dot v: I-> X$ from $a$ to $c$ given by
    $
    (u dot v)(t) = cases(
        u(2t) "if " 0<= t <= 1/2 ,
        v(2t-1) "if " 1/2 < t <= 1,
    )
    $
]

#definition[
    Let $u$ be a curve from $a$ to $b$. The inverse of $u$ is the curve $u^(-1)$ from $b$ to $a$ given by $u^(-1)(t) = u(1-t)$ for every $t in I$.
]

#theorem[
    If $u tilde.op u'$ and $v tilde.op v'$, then $u dot v tilde.op u'dot v'$ and $u^(-1) tilde.op (u')^(-1)$.
    
]
#proof[
    Let $A$ be a homotopy from $u$ to $u'$ and $B$ be a homotopy from $v$ to $v'$. Define a continuous map $C: I times I-> X$ by
    $
    C(t, s) = cases(
        A(2t, s) "if " 0<= t <= 1/2,
        B(2t-1, s) "if " 1/2 < t <= 1,
    )
    $
    Then $C$ is a homotopy from $u dot v$ to $u'dot v'$, which shows that $u dot v tilde.op u'dot v'$.

    Define a continuous map $D: I times I-> X$ by $D(t, s) = A(1-t, s)$. Then $D$ is a homotopy from $u^(-1)$ to $(u')^(-1)$, which shows that $u^(-1) tilde.op (u')^(-1)$.
    $qed$
]

#definition[
    A curve $u$ is closed if $u(0) = u(1)$. A curve $u$ is constant if $u(t) = u(0)$ for every $t in I$. A constant curve at $a$ may be denoted simply by $a$.
]

#theorem[
    The set $pi_1(X, a)$ of homotopy classes of closed curves at $a$ forms a group under the product operation, called the fundamental group of $X$ at $a$.
    
]
#proof[
    The identity element of $pi_1(X, a)$ is the homotopy class of the constant curve at $a$. To see this, for every curve $u$ from $a$ to $a$, construct a homotopy $A: I times I-> X$ from $u dot a$ to $u$ by
    $
    A(t, s) = cases(
        u((2t)/(1+s)) "if " 0<= t <= (1+s)/2 ,
        a "if " (1+s)/2 < t <= 1,
    )
    $
    The case for $a dot u$ is similar. For every curve $u$ from $a$ to $a$, construct a homotopy $B: I times I-> X$ from $u dot u^(-1)$ to $a$ by
    $
    B(t, s) = cases(
        u((2t)/(1-s)) "if " 0<= t <= 1/2 ,
        u((2(1-t))/(1-s)) "if " 1/2 < t <= 1,
    )
    $

    For curves $u, v, w$ from $a$ to $a$, construct a homotopy $C: I times I-> X$ from $(u dot v)dot w$ to $u dot (v dot w)$ by
    $
    C(t, s) = cases(
        u((4t)/(s+1)) "if " 0<= t <= (s+1)/4 ,
        v(4t-s-1) "if " (s+1)/4 < t <= (s+2)/4 ,
        w((4t-s-2)/(2-s)) "if " (s+2)/4 < t <= 1,
    )
    $
    Hence the product operation on $pi_1(X, a)$ is associative.
    $qed$
]

Denote the homotopy class of a curve $u$ by $"cl"(u)$.

#remark[
    If $X$ is arcwise connected, then $pi_1(X, a)$ is independent of the choice of $a$ up to isomorphism. To see this, let $b in X$ and $u$ be a curve from $a$ to $b$. Define a map $Phi: pi_1(X, a)-> pi_1(X, b)$ by $Phi("cl"(v)) = "cl"(u^(-1)dot v dot u)$ for every closed curve $v$ at $a$, then $Phi$ is a group isomorphism.
]

#definition[
    An arcwise connected space $X$ is simply connected if $pi_1(X, a) = 0$.
]

#definition[
    Suppose $u, v$ are two close curves whose initial point are not necessarily the same. We say that $u$ and $v$ are free homotopic if there exists a continuous map $A: I times I-> X$ such that
    
    + $A(t, 0) = u(t)$ for every $t in I$;
    + $A(t, 1) = v(t)$ for every $t in I$;
    + $A(0, s) = A(1, s)$ for every $s in I$.
    
]

#theorem[
    The following are equivalent for an arcwise connected space $X$:
    
    + $X$ is simply connected;
    + for every $u, v$ from $a$ to $b$, we have $u tilde.op v$;
    + for every closed curve $u, v$ at $a, b$ respectively, we have $u$ and $v$ are free homotopic.
    
    
]
#proof[
    - (i) $=>$ (ii): Note that
    $
    u tilde.op a dot u tilde.op (v dot v^(-1)) dot u tilde.op v dot (v^(-1) dot u) tilde.op v dot b tilde.op v.
    $
    - (ii) $=>$ (iii): Let $w$ be a curve from $a$ to $b$. Then consider the concatenation of $u tilde.op a$, $a tilde.op b$ and $b tilde.op v$, where the middle map is given by $w$. This gives a free homotopy from $u$ to $v$.
    - (iii) $=>$ (i): For every closed curve $u$ at $a$, we have $"cl"(u) = "cl"(a)$, which implies that $pi_1(X, a) = 0$.
$qed$
]

#definition[
    Let $X, Y$ be topological spaces and $p: Y-> X$ be a continuous map. $p$ is a local homeomorphism if for every $in Y$, there exists an open neighborhood $V$ of $y$ such that $p(V)$ is open in $X$ and $p|_V: V-> p(V)$ is a homeomorphism. $p$ is a *covering map* if for every $x in X$, there exists an open neighborhood $U$ of $x$ such that $p^(-1)(U)$ is a disjoint union of open subsets of $Y$, each of which is homeomorphic to $U$ via $p$.
]

#theorem(id: "thm:curve_lifting", name: "Curve Lifting Property")[
    Let $X, Y$ be topological spaces and $p: Y-> X$ be a covering map. Let $u$ be a curve with initial point $x_0 in X$ and $y_0 in p^(-1)(x_0)$. Then there exists a curve $tilde(u)$ with initial point $y_0$ such that $p compose tilde(u) = u$.
    $
    #diagram(
        $
         & Y edge(->, "d", p, #left) \
        [0, 1] edge("-->", "ur", tilde(u)) edge(->, "r", u, #right) & X
        $
    )
    $
]
#proof[
    Let
    $
    J = { t in [0, 1] : u|_([0, t]) "can be lifted to a curve" tilde(u) "with initial point" y_0}.
    $
    $J != emptyset$ since $0in J$.

    For $t in J$, choose an open neighborhood $cal(U)$ of $u(t)$ such that $p^(-1)(cal(U)) = union.sq.big_(alpha) V_alpha$ and $p|_(V_alpha): V_alpha -> cal(U)$ is a homeomorphism for every $alpha$. Let $tilde(u)(t) in V_(alpha_0)$ for some $alpha_0$. Since $u$ is continuous, there exists $epsilon > 0$ such that $[t, t+epsilon] subset u^(-1)(cal(U))$. Let $phi.alt: cal(U) -> V_(alpha_0)$ be the inverse of $p|_(V_(alpha_0))$, then $phi.alt compose u|_([t, t+epsilon])$ is a lift of $u|_([t, t+epsilon])$ with initial point $tilde(u)(t)$. Hence $[t, t+epsilon] subset J$, which shows that $J$ is open.

    Suppose $\{ t_n \} subset J$ is a sequence such that $t_n -> t_0$ with $t_n < t_0$ for every $n$. Choose $u(t_0) in cal(U)$ as above. Assume that $u([t_n, t_0]) subset cal(U)$ and let $tilde(u)(t_n) in V_(beta_0)$ for some $beta_0$. Let $phi.alt = (p|_(V_(beta_0)))^(-1)$, then we can define $tilde(u)(t) = phi.alt compose u(t)$ for every $t in [t_n, t_0]$, thus $[t_n, t_0] subset J$. Hence $t_0 in J$, which shows that $J$ is closed.

    Since $J$ is nonempty, open and closed, we have $J = [0, 1]$, which shows the existence of $tilde(u)$.
    $qed$
]

#theorem(name: "Uniqueness")[ 
    Suppose $X, Y$ are Hausdorff topological spaces and $p: Y-> X$ is a local homeomorphism. Suppose $Z$ is connected and $f: Z-> X$ is a continuous map. If $tilde(f)_1, tilde(f)_2: Z-> Y$ are two lifts of $f$ such that $tilde(f)_1(z_0) = tilde(f)_2(z_0)$ for some $z_0 in Z$, then $tilde(f)_1 = tilde(f)_2$.
]
#proof[
    Let
    $
    G = \{ z in Z | tilde(f)_1(z) = tilde(f)_2(z) \}.
    $
    Then $G$ is nonempty since $z_0 in G$. $G$ is closed since it is the preimage $(tilde(f)_1, tilde(f)_2)^(-1)(delta)$ of the diagonal $delta$ in $Y times Y$. To show that $G$ is open, let $z in G$ and $y = tilde(f)_1(z) = tilde(f)_2(z)$. Choose a neighborhood $U$ of $y$ such that $p|_U: U-> p(U)$ is a homeomorphism. Since $tilde(f)_1, tilde(f)_2$ are continuous, there exists a neighborhood $W$ of $z$ such that $tilde(f)_i(W) subset.eq U$ for $i = 1, 2$. By definition of lift, $p compose tilde(f)_i = f => tilde(f)_i = (p|_U)^(-1) compose f$ on $W$, which implies that $tilde(f)_1 = tilde(f)_2$ on $W$. Hence $G$ is open.

    By the connectedness of $Z$, we have $G = Z$, which shows that $tilde(f)_1 = tilde(f)_2$.
    $qed$
]

#theorem(name: "Homotopy Lifting")[ 
    Suppose $X, Y$ are Hausdorff topological spaces and $p: Y-> X$ is a covering map. Suppose $u, v$ are curves from $a$ to $b$ in $X$ and $A: I times I-> X$ is a homotopy from $u$ to $v$. Then for every $hat(a) in p^(-1)(a)$, there exists a homotopy $tilde(A): I times I-> Y$ from the lift of $u$ with initial point $hat(a)$ to the lift of $v$ with initial point $hat(a)$ such that $p compose tilde(A) = A$.
]
#proof[
    By the curve lifting property (@thm:curve_lifting), for each $u_s(t) = A(t, s)$ there exists a lift $tilde(u)_s$ with $tilde(u)_s(0) = hat(a)$. Define $tilde(A)(t, s) := tilde(u)_s(t)$, then clearly $p compose tilde(A) = A$. It remains to show that $tilde(A)$ is continuous.

    Take a neighborhood $cal(U)$ of $hat(a)$ such that $U$ is homeomorphic to $p(cal(U))$ via $p$. Let $phi.alt = (p|_(cal(U)))^(-1)$. Since $A$ is continuous, there exists $epsilon > 0$ such that $A([0, epsilon]times I) subset p(cal(U))$. By uniqueness of lift, we have $tilde(u)_s(t) = phi.alt compose A(t, s)$ for every $(t, s) in [0, epsilon]times I$, which implies that $tilde(A)$ is continuous on $[0, epsilon]times I$.

    Now suppose that $tilde(A)$ is discontinuous at some point $(t, c)$, and let $t_0$ be the infimum of such $t$. Choose a neighborhood $cal V$ of $tilde(A)(t_0, c)$ such that $p|_(cal V): cal V -> p(cal V)$ is a homeomorphism. Again, let $phi.alt = (p|_(cal V))^(-1)$. Since $A$ is continuous, there exists $delta > 0$ such that $A(B_delta(t_0, c)) subset p(cal V)$. By uniqueness of lift, we have $tilde(A)(t, s) = phi.alt compose A(t, s)$ for every $(t, s) in B_delta(t_0, c)$ with $t < t_0$, which implies that $tilde(A)$ is continuous at $(t_0, c)$, a contradiction. Hence $tilde(A)$ is continuous on $I times I$.

    _Intuition: by uniqueness of lifting, the mapping $tilde(A)$ is locally given by $phi.alt compose A$, which is the composition of two continuous maps, hence $tilde(A)$ is locally continuous, hence continuous_
    $qed$
]

== Deck Transformations

#theorem(id: "thm:lifting_continuous_map", name: "Lifting of a continuous map")[
    Suppose $X, Y$ are Hausdorff topological spaces and $p: Y-> X$ is a covering map. Suppose $Z$ is simply connected and $f: Z-> X$ is a continuous map. Then for every $y_0 in p^(-1)(f(z_0))$, there exists a unique lift $tilde(f): Z-> Y$ of $f$ such that $tilde(f)(z_0) = y_0$.
]
#proof[
    Pick $z_0 in Z$, $x_0 = f(z_0)$ and $y_0 in p^(-1)(x_0)$. For every $z in Z$, choose a curve $u$ from $z_0$ to $z$ and $v = f compose u$. By the curve lifting property (@thm:curve_lifting), there exists a lift $tilde(v)$ of $v$ with initial point $y_0$. Define $tilde(f)(z) = tilde(v)(1)$.

    To show that $tilde(f)$ is well-defined, let $u'$ be another curve from $z_0$ to $z$ and $v' = f compose u'$. Since $Z$ is simply connected, we have $u tilde.op u'$, which implies that $v tilde.op v'$. By the homotopy lifting property, we have $tilde(v) tilde.op tilde(v)'$, which implies that $tilde(v)(1) = tilde(v)'(1)$, hence $tilde(f)(z) = tilde(v)(1) = tilde(v)'(1)$.

    To show that $tilde(f)$ is continuous, let $z in Z$ and $y = tilde(f)(z)$. Choose a neighborhood $cal(U)$ of $y$ such that $p|_(cal(U)): cal(U) -> p(cal(U))$ is a homeomorphism and let $phi.alt = (p|_(cal(U)))^(-1)$. Since $f$ is continuous, there exists a neighborhood $W$ of $z$ such that $f(W) subset p(cal(U))$. For every $w in W$, choose a curve $u$ from $z$ to $w$ and let $v = f compose u$. By the curve lifting property, there exists a lift $tilde(v)$ of $v$ with initial point $tilde(f)(z) = y$. By uniqueness of lift, we have $tilde(v)(1) = phi.alt compose f(w)$, which implies that $tilde(f)(w) = tilde(v)(1) = phi.alt compose f(w)$ for every $w in W$, hence $tilde(f)$ is continuous at $z$. Since $z$ is arbitrary, $tilde(f)$ is continuous on $Z$.
    $qed$
]

#remark[
    In the proof above, the only properties of $p$ that are used are that it is a local homeomorphism and has the curve lifting property.
]

#theorem[
    Let $X$ be a manifold, $Y$ be a Hausdorff topological space, then $p: Y-> X$ is a covering map if and only if $p$ is a local homeomorphism and has the curve lifting property.   
]
#proof[
    The forward direction is clear. For the backward direction, let $x_0 in X$ and choose a simply connected neighborhood $U$ of $x_0$ and consider the injection $f: U-> X$. By the previous theorem, for each $y_j in p^(-1)(x_0)$, there exists a lift $tilde(f): U-> Y$ of $f$ such that $tilde(f)(x_0) = y_j$. Let $V_j = tilde(f)(U)$, then $p|_(V_j): V_j -> U$ is a homeomorphism. It remains to show that $p^(-1)(U) = union.sq.big_j V_j$.

    If $y in V_i inter V_j$, then $tilde(f)_i$ and $tilde(f)_j$ are two lifts of $f$ such that $tilde(f)_i(x_0) = tilde(f)_j(x_0) = y_i$, which implies that $tilde(f)_i = tilde(f)_j$, hence $V_i = V_j$. For $y in p^(-1)(U)$, let $x = p(y)$ and choose a curve $u$ from $x_0$ to $x$, then there exists a lift $tilde(u)$ of $u$ with initial point $y_i$, which implies that $y in tilde(f)_i(U) = V_i$. Hence $p^(-1)(U) = union.sq.big_j V_j$, which shows that $p$ is a covering map.
    $qed$
]

#definition[
    Let $p: Y-> X$ be a covering map. A deck transformation of $p$ is a fiber-preserving homeomorphism $f: Y-> Y$, that is, $p compose f = p$.

    The set of deck transformations of $p$ forms a group under composition, called the deck transformation group of $p$, denoted by $"Deck" (Y/X)$.
]

#proposition[
    If $p: Y-> X$ is a covering map, then $p$ induces an injective group homomorphism $p_*: pi_1(Y, y_0) -> pi_1(X, x_0)$ for every $y_0 in Y$ and $x_0 = p(y_0)$.   
]
#proof[
    For every closed curve $u$ at $y_0$, $p compose u$ is a closed curve at $x_0$. Define $p_*("cl"(u)) = "cl"(p compose u)$, then $p_*$ is a well-defined group homomorphism. To show that $p_*$ is injective, let $u$ be a closed curve at $y_0$ such that $p_*("cl"(u)) = "cl"(p compose u) = 0$. By the homotopy lifting property, there exists a homotopy $tilde(A): I times I-> Y$ from $u$ to the constant curve at $y_0$ such that $p compose tilde(A) = A$, where $A$ is a homotopy from $p compose u$ to the constant curve at $x_0$. Hence $"cl"(u) = 0$, which shows that $p_*$ is injective.
    $qed$
]

#proposition[
    Let $p: Y-> X$ be a covering map. Let $"cl"(u) in pi_1(X, x_0)$ and $tilde(u)(0) = y_0$ for some, then $u in p_*(pi_1(Y, y_0))$ if and only if $tilde(u)(1) = y_0$.
]
#proof[
    If $u in p_*(pi_1(Y, y_0))$, then there exists a closed curve $v$ at $y_0$ such that $p compose v = u$. By uniqueness of lift, we have $tilde(u) = v$, which implies that $tilde(u)(1) = v(1) = y_0$.

    Conversely, if $tilde(u)(1) = y_0$, then $tilde(u)$ is a closed curve at $y_0$ such that $p compose tilde(u) = u$, which implies that $u in p_*(pi_1(Y, y_0))$.
    $qed$
]

#lemma[
    For two loops $u_1, u_2$ at $x_0$, $u_1 dot u_2^(-1) in p_*(pi_1(Y, y_0))$ if and only if the lifts of $u_1$ and $u_2$ with initial point $y_0$ have the same terminal point.
]
#proof[
    This follows from the previous proposition since $u_1 dot u_2^(-1) in p_*(pi_1(Y, y_0))$ if and only if the lift of $u_1 dot u_2^(-1)$ with initial point $y_0$ is a closed curve at $y_0$, which is the case if and only if the lifts of $u_1$ and $u_2$ with initial point $y_0$ have the same terminal point.
    $qed$
]

Let $p: Y-> X$ be a covering map. A curve $"cl"(u) in pi_1(X, x_0)$ acts on the fibers of $p$ in the following way: for every $y in Y$, exists a curve $v$ from $y_0$ to $y$, then $v$ is the unique lift of $p compose v$ with initial point $y_0$. Consider the lift $v'$ of $p compose v dot u$ with initial point $y_0$, then $v'(1)$ is the image of $y$ under the action of $"cl"(u)$. This action is well-defined if $Y$ is simply-connected, hence we have a group homomorphism $Phi: pi_1(X, x_0) -> "Deck" (Y/X)$.

#proposition[
    Two covering maps $p, p': Y-> X$ are said to be isomorphic if there exists a homeomorphism $f: Y-> Y$ such that $p' compose f = p$. Two covering maps $p, p': Y-> X$ are isomorphic if and only if $p_*(pi_1(Y, y_0)) = p'_*(pi_1(Y, y_0'))$ where $p(y_0) = p'(y_0')$.
]
#proof[
    "$=>$": Since $p = p' compose f$, for $v in pi_1(Y, y_0)$, we have
    $
    p_*("cl"(v)) = "cl"(p compose v) = "cl"(p' compose f compose v) = p'_*("cl"(f compose v)).
    $ Hence $p_*(pi_1(Y, y_0)) subset.eq p'_*(pi_1(Y, y_0'))$. Since $f$ is a homeomorphism, by symmetry, we have $p_*(pi_1(Y, y_0)) = p'_*(pi_1(Y, y_0'))$.

    "$<=$": Similar to the proof of @thm:lifting_continuous_map, for each $y in Y$, choose a curve $v$ from $y_0$ to $y$ and let $u = p compose v$. By the curve lifting property (@thm:curve_lifting), there exists a lift $tilde(u)$ of $u$ with initial point $y_0'$. Define $tilde(p)(y) = tilde(u)(1)$. The well-definedness follows from the assumption that $p_*(pi_1(Y, y_0)) = p'_*(pi_1(Y, y_0'))$. The continuity of $f$ follows from the same argument as in @thm:lifting_continuous_map.
    $
    #diagram(
        $
         & Y edge(->, "d", p', #left) \
        Y edge("-->", "ur", exists tilde(p)) edge(->, "r", p, #right) & X
        $
    )
    $
    By symmetry, there exists a continuous map $tilde(p)': Y-> Y$ such that $p compose tilde(p)' = p'$. By uniqueness of lift, we have $tilde(p)' compose tilde(p) = tilde(p) compose tilde(p)' = id_Y$, which shows that $p$ and $p'$ are isomorphic.
    $qed$
]

#definition[
    A covering map $p: Y-> X$ is Galois if the deck transformation group $"Deck" (Y/X)$ acts transitively on the fibers of $p$, i.e. for every $x in X$ and $y_1, y_2 in p^(-1)(x)$, there exists a deck transformation $f$ such that $f(y_1) = y_2$.
]

#proposition[
    Given a covering map $p: Y-> X$, its deck transformation group is isomorphic to
    $
    "Deck" (Y/X) tilde.equiv N(pi_1(Y, y_0))/p_*(pi_1(Y, y_0)),
    $
    where $N(pi_1(Y, y_0))$ is the normalizer of $p_*(pi_1(Y, y_0))$ in $pi_1(Y, y_0)$. Moreover, $p$ is Galois if and only if $p_*(pi_1(Y, y_0))$ is a normal subgroup of $pi_1(X, x_0)$, in which case we have $"Deck" (Y/X) tilde.equiv pi_1(X, x_0)/p_*(pi_1(Y, y_0))$.
]
#proof[
    For each path $u in N(pi_1(Y, y_0))$, define a deck transformation $f_u: Y-> Y$ by $f_u(y) = tilde(u)(1)$, where $tilde(u)$ is the lift of $p compose u$ with initial point $y$. The well-definedness of $f_u$ follows from the definition of normalizer. The map $Phi: N(pi_1(Y, y_0)) -> "Deck" (Y/X)$ given by $Phi(u) = f_u$ is a group homomorphism since $f_(u dot v) = f_u compose f_v$ for every $u, v in N(pi_1(Y, y_0))$. The kernel of $Phi$ is exactly $p_*(pi_1(Y, y_0))$, hence $Phi$ induces an injective group homomorphism $tilde(Phi): N(pi_1(Y, y_0))/p_*(pi_1(Y, y_0)) -> "Deck" (Y/X)$. To show that $tilde(Phi)$ is surjective, let $f$ be a deck transformation of $p$. For every $in Y$, choose a curve $v$ from $y_0$ to $y$, then there exists a lift $tilde(v)$ of $p compose v$ with initial point $y_0$. Let $u = f compose tilde(v)$, then $p compose u = p compose f compose tilde(v) = p compose tilde(v) = p compose v$, which implies that $u$ is a lift of $p compose v$ with initial point $y_0$. By uniqueness of lift, we have $u = tilde(v)$, which implies that $f(y) = u(1) = tilde(v)(1) = y$. Hence $f$ is the identity map on $Y$, which shows that $tilde(Phi)$ is surjective.
    $qed$
]

== The Universal Covering

Recall that if $p: Y-> X$ is a covering map and $p_*(pi_1(Y, y_0)) triangle.l pi_1(X, x_0)$, then $p$ is Galois and the action of $pi_1(X, x_0)$ on the fibers of $p$ is well-defined.

#definition[
    $p: Y-> X$ is a universal covering of $X$ if for all covering map $p': Y'-> X$, there exists a continuous map $f: Y-> Y'$ such that $p' compose f = p$.
]

#proposition[
    If $Y$ is simply connected, then a covering map $p: Y-> X$ is universal, Galois and $"Deck" (Y/X) tilde.equiv pi_1(X, x_0)$.
]
#proof[
    Existence of lifting follows from @thm:lifting_continuous_map. Since $p_*(pi_1(Y, y_0)) = 0$, $p$ is Galois and $"Deck" (Y/X) tilde.equiv pi_1(X, x_0)$.
    $qed$
]

#theorem[
    If $X$ is a connected manifold and $H <= pi_1(X, x_0)$ is a subgroup, then there exists a covering map $p: Y-> X$ such that $p_*(pi_1(Y, y_0)) = H$ for some $y_0 in Y$ with $p(y_0) = x_0$.
]
#proof[
    Let
    $
    Y = \{ (x, \[ \[ u \] \]) | \[ \[ u \] \] "is equiv class of curves" u: x_0 |-> x "under" u tilde.op v "if" u dot v^(-1) in H \}).
    $
    Define a manifold structure on $Y$ as follows: for each $y = (x, \[ \[ u \] \]) in Y$ and an open ball $U_x$ around $x$, let
    $
    \[ U_x, y \] := \{ (z, \[ \[ u dot v \] \]) | z in U_x, v: x|-> z " is contained in" U_x \}.
    $

    We first show that the collection $\{ \[U_x, y \] | in Y \}$ forms a basis of topology on $Y$. Let $y_1 = (x_1, \[ \[ u_1 \] \]), y_2 = (x_2, \[ \[ u_2 \] \]) in Y$ and say $y_0 in \[ U_(x_1), y_1 \] inter \[ U_(x_2), y_2 \]$. We can write $y_0 = (z_0, \[ \[ u_1 dot v_1 \] \])$ for some curve $v_1$ from $x_1$ to $z_0$ contained in $U_(x_1)$ and $y_0 = (z_0, \[ \[ u_2 dot v_2 \] \])$ for some curve $v_2$ from $x_2$ to $z_0$ contained in $U_(x_2)$. By definition, $(u_1 dot v_1) tilde.op (u_2 dot v_2)$ in $H$. Consider a smaller open ball $W$ around $z_0$ such that $W subset.eq U_(x_1) inter U_(x_2)$, then for every $y in (W, y_0)$, there exists a curve $w$ from $z_0$ to $z$ contained in $W$ such that $y = (z, \[ \[ u_1 dot v_1 dot w \] \]) = (z, \[ \[ u_2 dot v_2 dot w \] \])$, which implies that $y in \[U_(x_1), y_1\] inter \[U_(x_2), y_2\]$. Hence $\{ \[U_x, y \] | in Y \}$ forms a basis of topology on $Y$.

    Now we show that $Y$ is Hausdorff. It suffices to prove that for $y_1 = (x, \[ \[ u_1 \] \]), y_2 = (x, \[ \[ u_2 \] \]) in Y$ with $\[ \[ u_1 \] \] != \[ \[ u_2 \] \]$, there exist $U_x$ such that $\[U_x, y_1\] inter \[U_x, y_2\] = emptyset$. If not, then exists $(z, r) in \[U_x, y_1\] inter \[U_x, y_2\]$. By definition, $r = [ [ u_1 dot v_1 ] ]$ for some curve $v_1$ from $x$ to $z$ contained in $U_x$ and $r = [ [ u_2 dot v_2 ] ]$ for some curve $v_2$ from $x$ to $z$ contained in $U_x$. Since $v_1, v_2$ are both contained in $U_x$, we have $v_1 tilde.op v_2$, which implies that $u_1 dot v_1 tilde.op u_2 dot v_2$, hence $\[ \[ u_1 \] \] = \[ \[ u_2 \] \]$, a contradiction. Hence $Y$ is Hausdorff.

    Define $p: Y-> X$ by $p(x, \[ \[ u \] \]) = x$. Suppose $u$ is a curve from $x_0$ to $x$. Let $u_s$ be the curve from $x_0$ to $u(s)$ given by $u_s(t) = u(s t)$, then
    $
    hat(u): [0, 1]-> Y, quad  t |-> (u(t), \[ \[ v dot u_t \] \])
    $
    is a lift of $u$ with initial point $(x_0, \[ \[ x_0 \] \])$. Hence $p$ has the curve lifting property. Since $p$ is a local homeomorphism, $p$ is a covering map. Finally, by definition, we have 
    $p_* ( pi_1 ( Y, (x_0, \[ \[ x_0 \] \] )) = H$.
    $qed$
]

From the construction above, we can see that the universal covering of $X$ is given by taking $H = 0$. Since universal covering is unique up to isomorphism, we know that $p: Y-> X$ is the universal covering of $X$ if and only if $Y$ is simply connected.

#remark[
    Given a universal covering $p: tilde(X) -> X$ and a covering $p': Y-> X$, the lifting $f: tilde(X) -> Y$ such that $p' compose f = p$ is in fact also a covering map.
]

#remark[
    A covering $p: Y-> X$ is Galois iff $pi_1(Y, y_0) triangle.l pi_1(X, x_0)$, in this case $"Deck" (Y/X) tilde.equiv "Deck" (tilde(X)/X)/pi_1(Y, y_0)$, where $tilde(X)$ is the universal covering of $X$. Hence the Galois coverings of $X$ are in one-to-one correspondence with the normal subgroups of $pi_1(X, x_0)$.
]

== Covering for Riemann Surfaces

#definition[
    A topological space $X$ is locally compact if it is Hausdorff and every point has a compact neighborhood. A continuous map $f: X-> Y$ is proper if $X, Y$ are locally compact and $f^(-1)(K)$ is compact for every compact subset $K$ of $Y$.
]

#proposition[
    A proper map is closed.
]
#proof[
    Recall that in a locally compact space, a subset is closed iff its intersection with every compact subset is compact. Let $f: X-> Y$ be a proper map and $A$ be a closed subset of $X$. For every compact subset $K$ of $Y$, we have
    $
    f(A)inter K = f(A inter f^(-1)(K)),
    $
    which is compact since $A inter f^(-1)(K)$ is compact and $f$ is continuous. Hence $f(A)$ is closed.
    $qed$
]

#proposition[
    If $p: Y-> X$ is proper and discrete, then $forall x in X$, $p^(-1)(x)$ is finite.
]
#proof[
    Since $p$ is discrete, for every $x in X$, $p^(-1)(x)$ is discrete and compact, hence $p^(-1)(x)$ is finite.
    $qed$
]

#theorem[
    If $p: Y-> X$ is proper and a local homeomorphism, then $p$ is a covering map.
]
#proof[
    Let $x in X$ and $p^(-1)(x) = \{ y_1, dots.h, y_n \}$. Since $p$ is a local homeomorphism, for each $y_j$, there exists a neighborhood $W_j$ of $y_j$ such that $p|_(W_j): W_j -> p(W_j)$ is a homeomorphism. Since $Y$ is Hausdorff, we can choose $W_j$ such that $\{ W_j \}$ are pairwise disjoint. Let $V = W_1 union dots.h union W_n$ and $cal(U) = inter.big_(j=1)^n p(W_j)$, then $p^(-1)(cal(U)) subset.eq V$. Set $V_j = W_j inter p^(-1)(cal(U))$, then $p|_(V_j): V_j -> cal(U)$ is a homeomorphism for every $j$ and $p^(-1)(cal(U)) = union.sq.big_(j=1)^n V_j$, which shows that $p$ is a covering map.
    $qed$
]

We now assume that $X, Y$ are Riemann surfaces and $p: Y-> X$ is a non-constant holomorphic map.

By the identity theorem $p^(-1)(x)$ is discrete for every $x in X$.

#definition[
    A point $y in Y$ is a branch point of $p$ if there does not exist a neighborhood $U$ of $y$ such that $p|_U$ is injective. A non-constant holomorphic map $p: Y-> X$ is unbranched if it has no branch point.
]

#proposition[
    A non-constant holomorphic map $p: Y-> X$ is unbranched iff it is a local homeomorphism.
]
#proof[
    "$=>$": For $y in Y$, exist a neighborhood $U$ of $y$ such that $p|_U$ is injective. Since $p$ is holomorphic, by the open mapping theorem, $p(U)$ is open in $X$, which implies that $p|_U: U-> p(U)$ is a homeomorphism.
    "$<=$": By definition, $p$ has no branch point.
    $qed$
]

#lemma[
    A proper unbranched holomorphic map $p: Y-> X$ is a covering map.
]
#proof[
    Since $p$ is proper and a local homeomorphism, $p$ is a covering map.
    $qed$
]

In general, let $A$ be the set of branch points of $p$, then $A$ is closed and discrete. Let $B = p(A)$ be the set of critical values of $p$.

#proposition[
    If $p$ is proper, then $p: Y without p^(-1)(B) -> X without B$ is an unbranched holomorphic covering map.
]
#proof[
    Since $p$ is proper, $p^(-1)(B)$ is compact, hence $Y without p^(-1)(B)$ is open. Since $B$ is discrete, $X without B$ is open. By definition of branch point, $p: Y without p^(-1)(B) -> X without B$ is a local homeomorphism. Since $p$ is proper, $p: Y without p^(-1)(B) -> X without B$ is a covering map.
    $qed$
]

Note that the fibers of a covering map have the same cardinality, hence we say $p: Y-> X$ is an $n$-sheeted covering if $|p^(-1)(x)| = n$ for every $x in X$.

#theorem[
    Let $DD = \{ z in CC | |z| < 1 \}$ be the unit disk. If $p: X-> DD$ is a proper non-constant holomorphic map, which is unbranched on $DD^* := DD without \{ 0 \}$, then $p$ is isomrophic to the map $DD -> DD, z|-> z^k$ for some $k in NN$.
]
#proof[
    Let $X^* = p^(-1)(DD^*)$, then $p: X^* -> DD^*$ is an unbranched holomorphic covering map. Let $H = \{ z in CC | "Re" (z) < 0 \}$ be the left half-plane, then the map $"exp": H -> DD^*$ is a universal covering of $DD^*$. Hence there exists a lift $f: H -> X^*$ of $"exp"$ such that $p compose f = "exp"$. Moreover, $X^*$ is isomorphic to $H/G$, where $G$ is a subgroup of $"Deck" (H/DD^*) tilde.equiv pi_1(DD^*) tilde.equiv ZZ$.

    If $G = 0$, then $X^* tilde.equiv H$, which implies that $p$ has an infinite fiber, contradicting the fact that $p$ is proper. Hence $G = k ZZ$ for some $k in NN$. Let $p_k$ denote the map $p_k: DD^* -> DD^*, z |-> z^k$. Note that $p_*(pi_1(X^*, x_0)) = p_(k*)(pi_1(DD^*, z_0))$, hence $p$ and $p_k$ are isomorphic as covering maps. Since $p$ and $p_k$ are locally biholomorphic, the isomorphism between $p$ and $p_k$ is in fact a local biholomorphism, hence an isomorphism of holomorphic covering maps. It now remains to show that $p$ can be extended to a holomorphic map on $X$.

    If $p^(-1)(0) = \{ b_1, dots.h, b_n \}$, then exists disjoint neighborhoods $V_i$ of $b_i$ and $B_r(0)$ of $0$ such that $p^(-1)(B_r(0)) subset.eq union.big_(i=1)^n V_i$. However, $p^(-1)(B_r(0)^*) tilde.equiv p_k^(-1)(B_r(0)^*) = B_(root(k, r))(0)^*$, which is connected, hence $p^(-1)(B_r(0))$ is connected, which implies that $n = 1$. Thus $p^(-1)(0) = \{ b_1 \}$, which implies that $p|_(X^*)$ can be extended to a holomorphic map on $X$ by defining $p(b_1) = 0$. Hence $p$ is isomorphic to the map $DD -> DD, z|-> z^k$ for some $k in NN$.
    $qed$
]

#definition[
    Let $X$ be a Riemann surface and $a in X$. Define the stalk of holomorphic functions at $a$ to be the set of equivalence classes of $f in cal(O)(U)$ where $U$ is a neighborhood of $a$, under the equivalence relation $f tilde.op g$ if there exists a neighborhood $W$ of $a$ such that $W subset.eq U inter V$ and $f|_W = g|_W$. The stalk of holomorphic functions at $a$ is denoted by $cal(O)_a$. Let $rho_a: cal(O)(U) -> cal(O)_a$ be the natural map given by $rho_a(f) = [f]$.
]

#definition[
    Let
    $
    |cal(O)| := union.sq.big_(a in X) cal(O)_a
    $
    be the disjoint union of stalks of holomorphic functions on $X$. Define a basis of topology on $|cal(O)|$ as follows: for each $U subset.eq X$ and $f in cal(O)(U)$, let
    $
    [U, f] := \{ rho_x(f) | x in U \} subset.eq |cal(O)|.
    $
    Let $p: |cal(O)| -> X$ be the natural map given by $p(rho_x(f)) = x$.
]


#proposition[
    The collection $cal B$ of all sets $[U, f]$ forms a basis of topology on $|cal(O)|$.
]

#proof[
    If $phi.alt in [U, f] inter [V, g]$, $p(phi.alt) = x in U inter V$ and $phi.alt = rho_x(f) = rho_x(g)$, then there exists a neighborhood $W$ of $x$ such that $W subset.eq U inter V$ and $f|_W = g|_W$, which implies that $[W, f] = [W, g] subset.eq [U, f] inter [V, g]$. Hence $cal B$ forms a basis of topology on $|cal(O)|$.

    Let $phi.alt_1, phi.alt_2 in |cal(O)|$ be distinct germs of holomorphic functions at $x_1, x_2$ respectively. If $x_1 != x_2$, then just take disjoint neighborhoods of $x_1$ and $x_2$. If $x_1 = x_2 = x$, let $rho_x(f_1) = phi.alt_1$ and $rho_x(f_2) = phi.alt_2$ with $f_1, f_2 in cal(O)(U)$ for some neighborhood $U$ of $x$. Then $[U, f_1|_U]$ and $[U, f_2|_U]$ are disjoint neighborhoods of $phi.alt_1$ and $phi.alt_2$ respectively. Hence $|cal(O)|$ is Hausdorff.
    $qed$
]

#proposition[
    $p: |cal(O)| -> X$ is a local homeomorphism and hence inherits a complex structure from $X$ such that $p$ is holomorphic.
]
#proof[
    For $phi.alt = rho_x(f) in |cal(O)|$, let $U$ be a neighborhood of $x$ such that $f in cal(O)(U)$, then $p|_([U, f]): [U, f] -> U$ is a homeomorphism with inverse given by $x' |-> rho_(x')(f)$, which shows that $p$ is a local homeomorphism. Hence we can define a complex structure on $|cal(O)|$ by taking the pullback of the complex structure on $X$ via $p$, which makes $p$ holomorphic.
    $qed$
]

Let $X$ be a Riemann surface and $a in X$, $phi.alt in cal(O)_a$. We want to find a maximal analytic continuation of $phi.alt$.

Let $Y$ be the connected component of $|cal(O)|$ containing $phi.alt$, then $Y$ is a Riemann surface and $p: Y-> X$ is locally biholomorphic. Define the function
$
f: Y -> CC, quad  psi |-> psi(p(psi)).
$
Then $f$ is well-defined and holomorphic. Moreover, $p_*(rho_psi(f)) = psi$.

== Analytic Continuation

Let $X$ be a Riemann surface and $a in X$, $phi.alt in cal(O)_(X, a)$. Let $Y$ be the connected component of $|cal(O)|$ containing $phi.alt$, then $Y$ is a Riemann surface and $p: Y-> X$ is locally biholomorphic and induces an isomorphism $p^*: cal(O)_(X, x) -> cal(O)_(Y, y)$ for every $y in Y$ with $p(y) = x$. Define the function
$
f: Y -> CC, quad  psi |-> psi(p(psi)).
$
Then $f$ is well-defined and holomorphic. Moreover, $p_*(rho_psi(f)) = psi$. Hence $f$ is a maximal analytic continuation of $phi.alt$.

In this section, we give a more concrete construction of analytic continuation of $phi.alt$ along curves.

Let $v: I -> Y$ be a curve with $v(0) = phi.alt$. Let $u = p compose v$, then $u$ is a curve in $X$ with $u(0) = a$. For each $t in I$, let $phi.alt_t$ be the germ of holomorphic functions at $u(t)$ given by $phi.alt_t = p_*(rho_(v(t))(f))$, then $phi.alt_0 = phi.alt$.

For $t_0 in I$, exists $V_0 subset Y$ such that $v(t_0) in V_0$ and $U_0 = p(V_0)$ is a neighborhood of $u(t_0)$ such that $p|_(V_0): V_0 -> U_0$ is a homeomorphism, and let $q := (p|_(V_0))^(-1): U_0 -> V_0$. Let $g_0 = q^*(f|_(V_0)) in cal(O)(U_0)$, then $p_*(rho_eta(f)) = rho_(p(eta))(g_0)$ for every $eta in V_0$. Since $v$ is continuous, there exists a neighborhood $T_0 subset I$ of $t_0$ such that $v(T_0) subset V_0$, i.e. $u(T_0) subset U_0$. For all $t in T_0$, we have $phi.alt_t = p_*(rho_(v(t))(f)) = rho_(p(v(t)))(g_0) = rho_(u(t))(g_0)$. Since $I$ is compact, exists $0 = t_0 < t_1 < dots.h < t_n = 1$ and for each $i$, there exists $V_i$ such that $v(t_i) in V_i$ and $U_i = p(V_i)$ is a neighborhood of $u(t_i)$ such that $p|_(V_i): V_i -> U_i$ is a homeomorphism, and let $g_i = (p|_(V_i))^*(f|_(V_i)) in cal(O)(U_i)$, then for each $t in [t_(i-1), t_i]$, we have $phi.alt_t = p_*(rho_(v(t))(f)) = rho_(p(v(t)))(g_i) = rho_(u(t))(g_i)$. Hence $phi.alt_1$ is the analytic continuation of $phi.alt$ along the curve $u$.

#definition[
    Suppose $X$ is a Riemann surface and $a in X$, $phi.alt in cal(O)_a$. A quadrupel $(Y, p, f, b)$ is called a analytic continuation of $phi.alt$ if
    
    + $Y$ is a Riemann surface and $p: Y-> X$ is an unbranched holomorphic covering map;
    + $f$ is a holomorphic on $Y$;
    + $b$ is a point of $Y$ such that $p(b) = a$ and
    $
    p_*(rho_b(f)) = phi.alt.
    $
    
    An analytic continuation $(Y, p, f, b)$ of $phi.alt$ is maximal if for any analytic continuation $(Z, q, g, c)$ of $phi.alt$, there exists a holomorphic map $F: Z -> Y$ such that $p compose F = q$, $F(c) = b$ and $F^*(f) = g$.
]

#remark[
    The construction $(Y, p, f, phi.alt)$ from the sheaf of holomorphic functions gives a maximal analytic continuation of $phi.alt$. For another analytic continuation $(Z, q, g, c)$ of $phi.alt$, define $F: Z-> Y$ as follows: for $z in Z$, let $q(z) = x$. Since $Y$ consists of all germs obtained by analytic continuation of $phi.alt$, there exists $eta in Y$ such that $q_*(rho_z(g)) = eta$. Define $F(z) = eta$, then $p compose F(z) = p(eta) = q(z)$ and $F^*(f) = g$ by definition of $f$.
]

#theorem[
    Let $X$ be a Riemann surface and $A$ be a discrete closed subset of $X$. Let $X' = X without A$. Let $pi': Y' -> X'$ be a proper unbranched holomorphic covering map, then exists a Riemann surface $Y$ and a proper holomorphic map $pi: Y-> X$ such that $pi' compose phi.alt = pi$ on $Y without pi^(-1)(A)$, where $phi.alt$ is a biholomorphism from $Y without pi^(-1)(A)$ to $Y'$.
]
#proof[
    Let $A = \{ a_i | i in Lambda \}$ and each $a_i$ has a neighborhood $U_i$ such that $U_i inter U_j = emptyset$ for $i != j$. Let $U_i^* = U_i without \{ a_i \}$. Since $pi': Y' -> X'$ is proper, $pi'^(-1)(U_i^*)$ is a disjoint union of finitely many connected components $V_(i j)$, each of which is biholomorphic to $U_i^*$ via $pi'$. Let $U_i$ be isomorphic to the unit disk $DD$ via $z_i$
    $
    #diagram(
        $
        V_(i j)^* edge(->, "r", phi.alt_(i j)^*) edge(->, "d", pi') & DD_i^* edge(->, "d", z mapsto z^(k_(i j)), #left) \
        U_i^* edge(->, "r", z_i, #right) & DD_i^*
        $
    )
    $
    Choose $P_(i j)$ for each $i in Lambda$ and $j = 1, dots.h n_i$, where $n_i$ is the number of connected components of $pi'^(-1)(U_i^*)$. The topology near $P_(i j)$ is given by the neighborhood basis $\{ P_(i j \}) union (pi'^(-1)(W_(i t)) inter V_(i j)^*)$ where $W_(i t), t in I_i$ is a neighborhood basis of $a_i$. The complex charts near $P_(i j)$ is given by the mappings $phi.alt_(i j): V_(i j) -> D_i$.
    $qed$
]

== Riemann Surfaces of Algebraic Functions

Algebraic functions are functions that satisfy a polynomial equation with coefficients in $cal(M)(X)$, the field of meromorphic functions on $X$. Most algebraic functions are multi-valued, hence we want to find a Riemann surface on which the algebraic function is single-valued.

#proposition(id: "prop:local_solution_of_polynomial_equation")[
    If $c_1, dots.h, c_n in cal(O)(B_R (0))$ are holomorphic functions on the disk $B_R (0)$, and $w_0 in CC$ is a simple zero of the polynomial
    $
    T^n + c_1(0)T^(n-1) + dots + c_n(0) in CC[T],
    $
    then there exists $0 < r <= R$ and a holomorphic function $phi.alt in cal(O)(B_r(0))$ such that $phi.alt(0) = w_0$ and
    $
    phi.alt^n + c_1phi.alt^(n-1) + dots + c_n = 0.
    $
]
#proof[
    For $z in B_R (0)$, $w in CC$, let
    $
    F(z, w) = w^n + c_1(z)w^(n-1) + dots + c_n(z).
    $
    By assumption, there exists $epsilon > 0$ such that $F(0, w)$ has a unique zero in $B_epsilon (w_0)$. Since $F(0, w) != 0$ on $partial B_epsilon (w_0)$, by continuity, there exists $0 < r <= R$ such that $F(z, w) != 0$ on $partial B_epsilon (w_0)$ for every $z in B_r(0)$. By the argument principle, for every $z_0 in B_r(0)$,
    $
    n(z_0) := (1)/(2pi i) integral_(partial B_epsilon (w_0)) ((partial F)/partial w(z_0, w))/(F(z_0, w)) d w
    $
    is the number of zeros of $F(z_0, w)$ in $B_epsilon (w_0)$ counting multiplicity. Since $n(z_0)$ is an integer-valued continuous function on $B_r(0)$, $n(z_0)$ is constant on $B_r(0)$. Since $n(0) = 1$, we have $n(z_0) = 1$ for every $z_0 in B_r(0)$. Recall that
    $
    (1)/(2pi i) integral_(partial B_epsilon (w_0)) (w (partial F)/partial z(z_0, w))/(F(z_0, w)) d w
    $
    is equal to the sum of zeros of $F(z_0, w)$ in $B_epsilon (w_0)$. Define $phi.alt(z_0)$ to be the above integral, then $phi.alt$ is holomorphic on $B_r(0)$ and $F(z_0, phi.alt(z_0)) = 0$ for every $z_0 in B_r(0)$.
     $qed$
]

#lemma[
    Let $X$ be a Riemann surface and $a in X$. If
    $
    overline(p)(T) = T^n + c_1T^(n-1) + dots + c_n in cal(O)_a[T]
    $
    and
    $
    p(T) := T^n + c_1(a)T^(n-1) + dots + c_n(a) in CC[T]
    $
    has $n$ distinct zeros $w_1, dots.h, w_n$, then there exists $phi.alt_1, dots.h, phi.alt_n in cal(O)_a$ such that $phi.alt_j(a) = w_j$ and
    $
    overline(p)(T) = product_(j=1)^n (T - phi.alt_j).
    $
]
#proof[
    Apply the above proposition to each $w_j$ iteratively, we can find $phi.alt_1, dots.h, phi.alt_n$ such that $phi.alt_j(a) = w_j$ and $overline(p)(T) = (T - phi.alt_1)dots (T - phi.alt_n)$ in $cal(O)_a[T]$.
    $qed$
]

Let $X, Y$ be Riemann surfaces and $pi: Y-> X$ be an n-sheeted holomorphic covering map. Let $f in cal(M)(Y)$. Fix a $x in X$ and a neighborhood $U$ of $x$ such that $pi^(-1)(U)$ is a disjoint union of $n$ connected components $V_1, dots.h, V_n$, each of which is biholomorphic to $U$ via $pi$. Let $tau_j: U -> V_j$ be the inverse of $pi|_(V_j)$, and let $f_i := tau_i^*f = f compose tau_i in cal(M)(U)$. Consider
$
product_(j=1)^n (T - f_j) = T^n + c_1T^(n-1) + dots + c_n in cal(M)(U)[T]
$
with $c_i = (-1)^i s_i(f_1, dots.h, f_n) in cal(M)(U)$ where $s_i$ is the $i$-th elementary symmetric polynomial. Let $x$ run through $X$ to get $c_i in cal(M)(X)$. Then $f$ satisfies the polynomial equation
$
f^n + c_1f^(n-1) + dots + c_n = 0
$
in the sense that for every $y in Y$, $x = pi(y)$ and $j$ such that $y in V_j$, we have
$
f(y)^n + c_1(x)f(y)^(n-1) + dots + c_n(x) = f_j(x)^n + c_1(x)f_j(x)^(n-1) + dots + c_n(x) = 0.
$

More generally, if $pi: Y-> X$ is now an $n$-sheeted branched holomorphic covering map. Let $A subset X$ be the set of critical values of $pi$ and $B = pi^(-1)(A)$. For $x in X without A$, we can define $f_j, c_i$ as above. If $c_i$ can be extended to holomorphic functions on $X$ for every $i$, then $f$ can also be extended to a holomorphic function on $Y$: for $a in A$, let $pi^(-1)(a) = \{ b_1, dots.h, b_m \}$ and let $pi^(-1)(U) = V$, $U inter A = \{ a \}$. For all $y in V without \{ b_1, dots.h, b_m \}$, we have
$
f(y)^n + c_1(pi(y))f(y)^(n-1) + dots + c_n(pi(y)) = 0,
$
which implies that $f(y)$ is bounded near $b_i$ for every $i$ iff $c_i$ is bounded near $a$ for every $i$.

Similarly, if $c_i$ can be extended to meromorphic functions on $X$ for every $i$, then $f$ can also be extended to a meromorphic function on $Y$.

#proposition(id: "prop:algebraic_extension_of_meromorphic_functions")[
    Let $X, Y$ be Riemann surfaces and $pi: Y-> X$ be an $n$-sheeted branched holomorphic covering map. Let $f, c_1, dots.h, c_n$ be constructed as above.
    
    + If $f in cal(M)(Y)$, then $f_n + (pi^*c_1)f^(n-1) + dots + (pi^*c_n) = 0$ in $cal(M)(Y)$.
    + Let $L := cal(M)(Y)$, $K := pi^*cal(M)(X)$, then $L/K$ is an algebraic extension of degree at most $n$.
    + If exists $x in X$ with $pi^(-1)(x) = \{ y_1, dots.h, y_n \}$ and some $f in cal(M)(Y)$ such that $f(y_i)$ are distinct for $i = 1, dots.h, n$, then $[L:K] = n$.
    
    Part (i) is clear by construction. For part (ii), note that $[K(f): K] <= n$ since $f$ satisfies a polynomial equation of degree $n$ with coefficients in $K$. Let $f_0 in cal(M)(Y)$ be such that $n_0 = [K(f_0): K]$ is maximal. For each $f in cal(M)(Y)$, since $"char" K = 0$, by the primitive element theorem, there exists $g in cal(M)(Y)$ such that $K(f, f_0) = K(g)$, then
    $
    [K(g): K] = [K(f, f_0): K] >= [K(f_0): K] = n_0 >= [K(g): K],
    $
    which implies that $n_0 = [K(g): K]$ and hence $f in K(g) = K(f_0)$, thus $L = K(f_0)$ and $[L:K] = n_0 <= n$.

    For part (iii), if $[K(f): K] = m <= n$, then $f$ satisfies a polynomial equation of degree $m$, say $f^m + pi^*g_1f^(m-1) + dots + pi^*g_m = 0$, then for all $x in X$, $y in pi^(-1)(x)$, $f(y)$ is a root of
    $
    T^m + g_1(x)T^(m-1) + dots + g_m(x) = 0,
    $
    which implies that $f$ takes at most $m$ distinct values on $pi^(-1)(x)$. By assumption, $f$ takes $n$ distinct values on $pi^(-1)(x)$, hence $m = n$ and $[L:K] = n$.
]

#theorem[
    Let $X$ be a Riemann surface and
    $
    p(T) = T^n + c_1T^(n-1) + dots + c_n in cal(M)(X)[T]
    $
    be a polynomial irreducible over $cal(M)(X)$, then there exists a Riemann surface $Y$, a $n$-sheeted branched holomorphic covering map $pi: Y-> X$ and $F in cal(M)(Y)$ such that $pi^*p(F) = 0$ in $cal(M)(Y)$. Moreover, $(Y, pi, F)$ is unique up to isomorphism in the sense that if $(Z, q, G)$ is another triple with the same property, then there exists a biholomorphism $f: Y -> Z$ such that $q compose f = pi$ and $f^*G = F$.
    $
    #diagram(
        $
        & Z edge(->, "d", q, #left) \
        Y edge(->, "ru", f) edge(->, "r", pi, #right) & X
        $
    )
    $
]
#proof[
    Since $"char" cal(M)(X) = 0$ and $p$ is irreducible over $cal(M)(X)$, the discriminant $delta in cal(M)(X)$ of $p$ is nonzero, hence the set zeros of $delta$ is discrete and closed. Let $A$ be the union of the set of zeros of $delta$ and the set of poles of $c_i$ for $i = 1, dots.h, n$, then $A$ is a discrete closed subset of $X$. Let $X' = X without A$. By definition, $c_i in cal(O)(X')$ and for all $x in X'$, $p(T) in cal(O)(X')[T]$ has $n$ distinct zeros, say $w_1, dots.h, w_n$. By @prop:algebraic_extension_of_meromorphic_functions, there exists a neighborhood $U_x$ of $x$ and $phi.alt_1, dots.h, phi.alt_n in cal(O)(U_x)$ such that $phi.alt_j(x) = w_j$ and $p(T) = product_(j=1)^n (T - phi.alt_j)$ in $cal(O)(U_x)[T]$.

    Let
    $
    Y' = \{ phi.alt in |cal(O)| : phi.alt in cal(O)_x, x in X', p(phi.alt) = 0 \}
    $
    and $pi': Y' -> X'$ be the natural map given by $pi'(phi.alt) = x$. $pi'$ is $n$ to $1$ hence proper, also $pi'^(-1)(U_x) = union.big_(j=1)^n [U_x, phi.alt_j]$ is a disjoint union of $n$ connected components (each root $w_j$ are distinct hence $phi.alt_j$ are distinct) each of which is biholomorphic to $U_x$ via $pi'$. Hence $pi': Y' -> X'$ is a proper unbranched holomorphic covering map. Let $f: Y' -> CC$ be given by $f(phi.alt) = phi.alt(pi'(phi.alt))$. Note that since $pi'_*(rho_phi.alt(f)) = phi.alt$ for every $phi.alt in Y'$, we have
    $
    pi'^*p(f) = p(pi'_*(rho_phi.alt(f))) = p(phi.alt) = 0
    $
    in $cal(M)(Y')$.

    By the above theorem, we can extend $pi': Y' -> X'$ to a proper holomorphic map $pi: Y-> X$, and $f$ can also be extended to a meromorphic function on $Y$, denoted by $F$, such that $pi^*p(F) = 0$ in $cal(M)(Y)$.

    If $Y$ is not connected, let $Y_1, dots.h, Y_k$ be the connected components of $Y$ with $k >= 2$ and $pi: Y_i -> X$ be $n_i$-sheeted coverings. From each $F|_(Y_i)$, we may construct a degree $n_i$ polynomial $P_i$ as in @prop:algebraic_extension_of_meromorphic_functions, then $p(T) = product_(i=1)^k P_i(T)$ in $cal(M)(X)[T]$, contradicting the irreducibility of $p$. Hence $Y$ is connected.

    For the uniqueness, let $(Z, q, G)$ be another triple with the same property. Let $B = \{ "poles of" G \} union \{ "the branched points of " tau \} subset Z$ and $A' = tau(B)$. Set $X'' = X' without A'$, $Y'' = tau^(-1)(X'')$ and $Z'' = q^(-1)(X'')$. Let $sigma$ map $G$ to $F$ by taking the germ of $G$ at $z in Z''$ to the germ of $F$ at $tau(z)$. Then $sigma$ is a well-defined holomorphic map from $Z''$ to $Y''$ such that $pi compose sigma = q$ and $sigma^*F = G$. Since $Z''$ is dense in $Z$, $sigma$ can be extended to a holomorphic map from $Z$ to $Y$, which is still denoted by $sigma$. Since $pi compose sigma = q$ and both $pi, q$ are proper, $sigma$ is proper. Since $pi compose sigma = q$, $sigma$ is injective, hence $sigma: Z -> Y$ is a biholomorphism with inverse given by the same construction by sending the germ of $F$ at $y in Y''$ to the germ of $G$ at $sigma^(-1)(y)$.
    $qed$
]

#remark[
    In fact, $"Deck" (Y/X) tilde.equiv "Gal"(L/K)$ where $L = cal(M)(Y)$ and $K = pi^*cal(M)(X)$, and the isomorphism is given by sending $sigma in "Deck" (Y/X)$ to the automorphism of $L$ over $K$ given by $f |-> sigma^*f$. Hence the Galois group of the algebraic extension $L/K$ can be interpreted as the group of deck transformations of the branched holomorphic covering map $pi: Y-> X$.
]

== Differential Forms

A differential 1-form on $B_r(0)$ can be written as $omega = f\, d x + g\, d y$ where $f, g in cal(E)(B_r(0))$ are smooth functions. The collection of all differential 1-forms on $B_r(0)$ is denoted by $cal(E)^((1))(B_r(0))$. $omega$ is closed iff $omega$ is closed iff $(partial F)/partial y = partial g/partial x$. $omega$ is exact iff there exists $F in cal(E)(B_r(0))$ such that $omega = d F = (partial F)/partial x\, d x + (partial F)/partial y\, d y$. exact implies closed, but in general closed does not imply exact.

Let $X$ be a Riemann surface, a differential 1-form on $X$ is a collection of differential 1-forms on each chart of $X$ such that they are compatible on the overlaps, i.e. on each char $U subset X$, $omega|_U = f\, d x + g\, d y$ where $f, g in cal(E)(U)$ are smooth functions. Given a covering map $p: Y-> X$ and a differential 1-form $omega$ on $X$, we can define the pullback $p^*omega$ of $omega$ on $Y$ by pulling back the local expressions of $omega$. Precisely, on a local chart $U$ with $p^(-1)(U) = union.big V_i$ where $V_i$ are disjoint and $p|_(V_i): V_i -> U$ is a homeomorphism, if $omega|_U = f\, d x + g\, d y$, then $(p^*omega)|_(V_i) = (f compose p)\, d(x compose p) + (g compose p)\, d(y compose p)$. Given a closed differential 1-form $omega$ on $X$, we would like to know whether there exists a holomorphic function $F$ on $Y$ such that $d F = p^*omega$.

#theorem[
    Suppose $X$ is a Riemann surface and $omega$ is a closed differential 1-form on $X$. Then there exists a covering map $p: Y-> X$ and a holomorphic function $F$ on $Y$ such that $d F = p^*omega$.
]
#proof[
    For $U subset X$, let
    $
    cal(F)(U) = \{ f in cal(E)(U) | d f = omega|_U \},
    $
    and let $cal(F)$ be the sheaf of $cal(E)$-modules on $X$ given by $U |-> cal(F)(U)$. Recall that $|cal(F)| = union.sq.big_(x in X) cal(F)_x$ is the disjoint union of stalks of $cal(F)$ on $X$.

    Consider the projection map $p: |cal(F)| -> X$ given by $p(rho_x(f)) = x$ where $rho_x(f)$ is the germ of $f$ at $x$. Locally, if $U$ is a neighborhood of $x$ isomorphic to the unit disk $DD$, so that there exists a local primitive $f in cal(F)(U)$, then $p^(-1)(U) = union.big_(c in CC) [U, f + c]$. Pick $Y$ to be a connected component of $|cal(F)|$, then $p: Y -> X$ is a local homeomorphism and hence inherits a complex structure from $X$ such that $p$ is holomorphic. Define $F: Y -> CC$ by $F(phi.alt) = phi.alt(p(phi.alt))$, then $F$ is well-defined and holomorphic, and $p_*(rho_phi.alt(F)) = phi.alt$ for every $phi.alt in Y$. Hence $d F = p^*omega$ on $Y$.
    $qed$
]

#lemma[
    Suppose $X$ is a Riemann surface and $pi: tilde(X) -> X$ is the universal covering map, then for every closed differential 1-form $omega$ on $X$, there exists a holomorphic function $F$ on $tilde(X)$ such that $d F = pi^*omega$.
]
#proof[
    Let $p: Y -> X$ and $F$ be given by the above theorem, Since $pi$ is the universal covering map, there exists a holomorphic map $tau: tilde(X) -> Y$ such that $p compose tau = pi$, hence $tau^*F$ is a holomorphic function on $tilde(X)$ such that $d(tau^*F) = tau^*d F = tau^*p^*omega = pi^*omega$.
    $qed$
]

#theorem[
    Suppose $X$ is a Riemann surface and $pi: tilde(X) -> X$ is the universal covering map. For every closed differential 1-form $omega$ on $X$, exists a primitive $F in cal(E)(tilde(X))$ of $pi^*omega$. If $c: I -> X$ is a curve and $tilde(c): I -> tilde(X)$ is a lift of $c$, then
    $
    integral_c omega = F(tilde(c)(1)) - F(tilde(c)(0))
    $
    is well-defined, i.e. independent of the choice of the primitive $F$ and the lift $tilde(c)$.
]
#proof[
    For another primitive $F' in cal(E)(tilde(X))$ of $pi^*omega$, we have $d(F - F') = 0$, hence $F - F'$ is a constant function on $tilde(X)$.

    Let $tilde(c)_1, tilde(c)_2: I -> tilde(X)$ be two lifts of $c$. Since $pi: tilde(X) -> X$ is Galois, there exists a deck transformation $sigma: tilde(X) -> tilde(X)$ such that $sigma compose tilde(c)_1 = tilde(c)_2$, hence
    $
    d(sigma^*F) = sigma^*d F = sigma^*pi^*omega = pi^*omega = d F,
    $
    which implies that $sigma^*F - F$ is a constant function on $tilde(X)$. Thus
    $
    F(tilde(c)_2(1)) - F(tilde(c)_2(0)) &= F(sigma compose tilde(c)_1(1)) - F(sigma compose tilde(c)_1(0)) \
    &= sigma^*F(tilde(c)_1(1)) - sigma^*F(tilde(c)_1(0)) = F(tilde(c)_1(1)) - F(tilde(c)_1(0)).
    $
    $qed$
]

#proposition[
    Let $X$ be a simply connected Riemann surface, then every closed differential 1-form on $X$ is exact.
]
#proof[
    The universal covering map of $X$ is the identity map, hence every closed differential 1-form on $X$ has a primitive on $X$.
    $qed$
]

#proposition[
    Let $X$ be a Riemann surface and $omega$ be a closed differential 1-form on $X$. Let $a, b in X$ and $u, v$ be two homotopic curves from $a$ to $b$, then $integral_u omega = integral_v omega$.
]
#proof[
    Since $u, v$ are homotopic, their liftings $tilde(u), tilde(v)$ with the same initial point are also homotopic, hence $tilde(u)(1) = tilde(v)(1)$, which implies that $integral_u omega = F(tilde(u)(1)) - F(tilde(u)(0)) = F(tilde(v)(1)) - F(tilde(v)(0)) = integral_v omega$.
    $qed$
]

#proposition[
    Let $X$ be a Riemann surface and $omega$ be a closed differential 1-form on $X$. Let $u, v$ be two closed curves that are free homotopic, then $integral_u omega = integral_v omega$.
]
#proof[
    Say $u, v$ are based on $a, b$ respectively, and let $w$ be a cuve from $a$ to $b$ such that $w dot v dot w^(-1) tilde.op u$, then
    $
    integral_u omega = integral_(w dot v dot w^(-1)) omega = integral_w omega + integral_v omega + integral_(w^(-1)) omega = integral_v omega.
    $
    $qed$
]

#theorem[
    Let $X$ be a Riemann surface and $pi: tilde(X) -> X$ be the universal covering map.
    
    +   Let $omega in cal(E)^((1))(X)$ be a closed differential 1-form on $X$ with primitive $d F = pi^*omega$, then for all $sigma in "Deck" (tilde(X)/X)$, define $sigma F = F compose sigma^(-1)$, then $sigma F$ is also a primitive of $pi^*omega$ and $F - sigma F$ is a constant function on $tilde(X)$. The constant equals
        $
        F - sigma F = integral_sigma omega
        $
        where $integral_sigma omega$ is understood by integrating along the curve associated to $sigma$ by the isomorphism $"Deck" (tilde(X)/X) tilde.equiv pi_1(X)$.
    +   If $F in cal(E)(tilde(X))$ such that for all $sigma in "Deck" (tilde(X)/X)$, exists a constant $c_sigma$ such that $F - sigma F = c_sigma$, then $d F$ is the pullback of a closed differential 1-form on $X$.
]

#proof[
    +   Let $F - sigma F = c$. Let $z_0, y_0$ be two points in $tilde(X)$ such that $sigma(y_0) = z_0$ and $v$ be a curve from $y_0$ to $z_0$, then $u = pi compose v$ is associated to $sigma$ by the isomorphism $"Deck" (tilde(X)/X) tilde.equiv pi_1(X)$. Hence
        $
        integral_sigma omega = integral_u omega = F(v(1)) - F(v(0)) = F(z_0) - F(y_0) = F(z_0) - sigma F(z_0) = c.
        $
    +   For every $sigma in "Deck" (tilde(X)/X)$,
        $
        sigma^*d F = d(sigma F) = d(F - c_sigma) = d F,
        $
        hence $d F$ is invariant under the action of $"Deck" (tilde(X)/X)$, which implies that $d F$ is the pullback of a closed differential 1-form on $X$.
    $qed$
]

== Linear Differential Equations

#theorem(name: "Local solution")[ 
    If $A in M(n times n, cal(O)(B_R (0)))$ is a matrix of holomorphic functions on the disk $B_R (0)$, then for every $w_0 in CC^n$, there exists a unique holomorphic function $w in M(n times 1, cal(O)(B_r(0)))$ such that $w'(z) = A(z)w(z)$ for every $z in B_R (0)$ and $w(0) = w_0$.
    
]

#proof[
        Expand into Taylor series for each entry of $A$, so that we can write
        $
        A(z) = sum_(\nu=0)^oo A_\nu z^\nu
        $
        where $A_\nu = (a_(i j\nu)) in M(n times n, CC)$ for every $\nu$. Suppose the solution has the form
        $
        w(z) = sum_(\nu=0)^oo c_\nu z^\nu
        $
        where $c_\nu = (c_(i\nu)) in CC^n$ for every $\nu$. If this series converges, then it should satisfy the equation $w'(z) = A(z)w(z)$, which is equivalent to
        $
        sum_(k=1)^oo k c_k z^(k-1) = (sum_(\nu=0)^oo A_\nu z^\nu) (sum_(\nu=0)^oo c_\nu z^\nu) = sum_(k=0)^oo (sum_(\nu=0)^k A_\nu c_(k-\nu)) z^k,
        $
        hence
        $
        (k+1) c_(k+1) = sum_(\nu=0)^k A_\nu c_(k-\nu)
        $
        for every $k >= 0$. Since $c_0 = w_0$ is given, we can determine $c_\nu$ for every $\nu$ inductively, uniqueness also follows from this. It now remains to show that the series converges.

        For arbitrary $0 < r < R$, the series
        $
        sum_(\nu=0)^oo |a_(i j\nu)| r^\nu
        $
        converges for every $i, j$, hence there exists $N > 0$ such that $|a_(i j\nu)| r^\nu <= N/r$, i.e. $|a_(i j\nu)| <= N/r^(\nu+1)$ for every $\nu$. Define
        $
        b_(i j)(z) = (N)/(r) (1 - (z)/(r))^(-1) = sum_(\nu=0)^oo (N)/(r^(\nu+1)) z^\nu,
        $
        which is holomorphic in $|z| < r$. Write $w_0 = (w_(i 0)) in CC^n$ and define $K = limits("max")_(1<= i <= n) |w_(i 0)|$. Define $psi(z) = K(1 - z/r)^(-N)$, which is holomorphic in $|z| < r$, then
        $
        psi'(z) = - N K (1 - z/r)^(-N-1) dot (-1/r) = (N)/(r) K (1 - z/r)^(-N-1) = b_(i j)(z) psi(z)
        $
        and satisfies $psi(0) = K$. Let $v(z) = (psi(z), dots.h, psi(z)) in CC^n$, then $v'(z) = b_(i j)(z) v(z)$ and $v(0) = (K, dots.h, K)$. Write
        $
        psi(z) = sum_(\nu=0)^oo psi_\nu z^\nu.
        $

        Note that $|a_(i j\nu)| <= N/r^(\nu+1) = b_(i j\nu)$. We show by induction that $|c_(i\nu)| <= psi_\nu$ for every $i, \nu$. For $\nu = 0$, $|c_(i 0)| = |w_(i 0)| <= K = psi_0$. Assume that $|c_(i\nu)| <= psi_\nu$ for every $i$ and $\nu <= k$, then
        $
        (k+1)|c_(i, k+1)| &= |( sum_(\nu=0 )|sum_(j=1)^n a_(i j\nu) c_(j, k-\nu)) \
        &<= sum_(\nu=0)^k sum_(j=1)^n |a_(i j\nu)| |c_(j, k-\nu)| \
        &<= sum_(\nu=0)^k sum_(j=1)^n b_(i j\nu) psi_(k-\nu) \
        &= (k+1) psi_(k+1),
        $
        which implies that $|c_(i, k+1)| <= psi_(k+1)$. Hence the series $sum_(\nu=0)^oo c_\nu z^\nu$ converges for every $|z| < r$, which completes the proof.
     $qed$
]

Let $omega(X)$ be the space of holomorphic 1-forms on a Riemann surface $X$, i.e. on every chart $U$, $omega$ can be written as $omega = f\, d z$ where $f in cal(O)(U)$.

#theorem[
    Let $X$ be a simply connected Riemann surface and $A in M(n times n, omega(X))$, $x_0 in X$, then for all $c in CC^n$, there exists a unique $w in cal(O)(X)^n$ is a solution of the equation $d w = A w$ with initial condition $w(x_0) = c$.
    
]

#proof[
        Note that locally we can write $A = F\, d z$ where $F in M(n times n, cal(O)(U_0))$ for some chart $U_0 tilde.equiv B_1(0)$. Hence the equation $d w = A w$ is equivalent to $d w/d z = w' = F w$, which has a unique local solution by the above theorem. Let $alpha: [0, 1] -> X$ be a curve with $alpha(0) = x_0$. If $alpha([0, t_1]) subset U_0$, then let $x_1 = alpha(t_1)$ and $c_1 = f(alpha(t_1))$, then by the above theorem again, exists a local solution $f_1 in cal(O)(U_1)^n$ with $U_1 tilde.equiv B_1(0)$ a neighborhood of $x_1$ such that $f_1(x_1) = c_1$. By the uniqueness of the local solution, $f$ and $f_1$ coincide on $U_0 inter U_1$, hence we can glue them together to get a solution on $U_0 union U_1$. Since $[0, 1]$ is compact, we can cover $alpha([0, 1])$ by finitely many charts $U_0, dots.h, U_k$ and glue the local solutions together to get a solution along the curve $alpha$. The maximal analytic continuation $(Y, p, F, y_0)$ of the local solution $f$ is a covering map, and since $X$ is simply connected, $Y tilde.equiv X$ and thus $F$ is a global solution on $X$.
     $qed$
]

#lemma[
    Let $p: tilde(X) -> X$ be the universal covering, $A in M(n times n, omega(X))$ and $c in CC^n$, then there exists a unique $w in cal(O)(tilde(X))^n$ is a solution of the equation $d w = (p^*A) w$ with initial condition $w(tilde(x)_0) = c$ where $tilde(x)_0 in tilde(X)$ is a lift of $x_0$.
    
]

#proof[
        Since $tilde(X)$ is simply connected, the equation $d w = (p^*A) w$ has a unique solution on $tilde(X)$ with the given initial condition by the above theorem.
     $qed$
]

#definition[
    Suppose $X$ is a Riemann surface and $A in M(n times n, omega(X))$. On the universal covering $p: tilde(X) -> X$, define
    $
    L_A := \{ w in cal(O)(tilde(X))^n : d w = (p^*A) w \},
    $
    then $L_A$ is an $n$-dimensional vector space over $CC$ and $w_1, dots.h, w_n in L_A$ are linearly independent iff $w_1(x_0), dots.h, w_n(x_0)$ are linearly independent for some $x_0 in tilde(X)$. We call $L_A$ the solution space of the equation $d w = A w$.
]

For a basis $w_1, dots.h, w_n$ of $L_A$, define a fundamental system of solutions to be
$
Phi := (w_1, dots, w_n) in "GL" (n, cal(O)(tilde(X))),
$
then $Phi$ satisfies $d Phi = (p^*A) Phi$.

Let $G = "Deck" (tilde(X)/X)$, then for any $sigma in G$, define $sigma Phi := Phi compose sigma^(-1)$, then
$
d(sigma Phi) = d(Phi compose sigma^(-1)) = (p^*A) (Phi compose sigma^(-1)) = (p^*A) sigma Phi,
$
hence $sigma Phi$ is also a fundamental system of solutions. Since $Phi$ is a fundamental system of solutions, there exists a unique $T_sigma in "GL"(n, CC)$ such that $sigma Phi = Phi T_sigma$. The matrices $T_sigma$ are called the factors of automorphy of $Phi$.

Consider the special case where $X = B_R (0)^*$ with $0 < R <= oo$ and $p: tilde(X) -> X$ be the universal covering. Note that $"exp": \{ "Re" z < log R \} -> X$ is also a universal covering, hence there exists a single-valued branch of $log$ on $tilde(X)$ such that $"exp" compose log = p$. Pick a generator $sigma in "Deck" (tilde(X)/X)$ such that $sigma compose log = log + 2pi i$, then the behavior of $Phi$ under deck transformations is determined by the factor of automorphy $T_sigma$. Recall that there exists $S in "GL"(n, CC)$ such that $S^(-1) T_sigma S$ is in Jordan normal form, then we can consider $Psi = Phi S$, so that
$
sigma Psi = sigma(Phi S) = sigma Phi S = Phi T_sigma S = Phi S (S^(-1) T_sigma S) = Psi (S^(-1) T_sigma S).
$

#definition[
    For a matrix $A in M(n times n, CC)$, define the exponential of $A$ by
    $
    e^A = sum_(k=0)^oo (A^k)/(k!).
    $
]

If $A, B in M(n times n, CC)$ commute, then $e^(A+B) = e^A e^B$. In particular $"exp"(A)"exp"(-A) = I$, hence $"exp"(A) in "GL" (n, CC)$. If $S in "GL" (n, CC)$, then $e^(S A S^(-1)) = S e^A S^(-1)$.

#proposition[
    For all $B in "GL" (n, CC)$, there exists $A in M(n times n, CC)$ such that $e^A = B$.
    
]

#proof[
        We may assume that $B$ is in Jordan normal form, and we may consider the blocks of $B$ separately. If $B = "diag"((Lambda_1, dots.h, Lambda_n))$ is diagonal, then we can take $A = "diag"((log Lambda_1, dots.h, log Lambda_n))$. If $B$ is a Jordan block of the form
        $
        B = mat(
            Lambda, 1, 0, dots, 0 ;
            0, Lambda, 1, dots, 0 ;
            dots.v, dots.v, dots.v, dots.down, dots.v ;
            0, 0, 0, dots, 1 ;
            0, 0, 0, dots, Lambda
        ),
        $
        then we can take
        $
        A = mu I_n + log (I_n + (1)/(Lambda) N) = mu I_n + sum_(k=1)^(n-1) ((-1)^(k-1))/(k Lambda^k) N^k
        $
        where $mu$ is a logarithm of $Lambda$ and $N$ is the nilpotent matrix given by
        $
        N = mat(
            0, 1, 0, dots, 0 ;
            0, 0, 1, dots, 0 ;
            dots.v, dots.v, dots.v, dots.down, dots.v ;
            0, 0, 0, dots, 1 ;
            0, 0, 0, dots, 0
        ).
        $
        Then
        $
        e^A = e^(mu I_n) e^(log (I_n + (1)/(Lambda) N)) = Lambda (I_n + (1)/(Lambda) N) = B.
        $
     $qed$
]

#theorem[
    Let $X = B_R (0)^*$. Let $T in "GL" (n, CC)$ and $B in M(n times n, CC)$ such that $"exp"(2 pi i B) = T$, then $Phi_0 := "exp"(B log) in "GL" (n, cal(O)(tilde(X)))$ is a fundamental system of solutions of
    $
    w' = (B)/(z) w
    $
    on the universal covering $p: tilde(X) -> B_R (0)^*$ such that $sigma Phi_0 = Phi_0 T$.
    
]

#proof[
        Note that
        $
        Phi_0' = (B)/(z) "exp"(B log) = (B)/(z) Phi_0,
        $
        and
        $
        sigma Phi_0 = sigma "exp"(B log) = "exp"(B sigma log) = "exp"(B (log + 2pi i)) = "exp"(B log) "exp"(2pi i B) = Phi_0 T,
        $
        hence proved.
     $qed$
]

#theorem[
    Let $X = B_R (0)^*$. Let $A in M(n times n, cal(O)(X))$, then $w' = A w$ has a fundamental system of solutions $Phi in "GL" (n, cal(O)(X))$ of the form
    $
    Phi = Psi Phi_0
    $
    where $Phi_0 = "exp"(B log)$ for a constant matrix $B$ and $Psi$ is invariant under heck transformations, i.e. $Psi$ defines an element in $"GL" (n, cal(O)(X))$.
    
]

#proof[
        Suppose $Phi$ is a fundamental system of solutions of $w' = A w$, and $sigma Phi = Phi T$ where $T in "GL" (n, CC)$. By the previous theorem exists $B in M(n times n, CC)$ such that $"exp"(2pi i B) = T$ and $Phi_0 = "exp"(B log)$ such that $sigma Phi_0 = Phi_0 T$. Let $Psi = Phi Phi_0^(-1)$, then
        $
        sigma Psi = sigma(Phi Phi_0^(-1)) = (sigma Phi) (sigma Phi_0)^(-1) = (Phi T) (Phi_0 T)^(-1) = Phi Phi_0^(-1) = Psi,
        $
        hence $Psi$ is invariant under deck transformations and defines an element in $"GL" (n, cal(O)(X))$.
     $qed$
]

== Big Theorem

Recall that $X = B_R (0)^*$, and universal covering $p: tilde(X) -> X$, $A in M(n times n, cal(O)(X))$, then $w' = A w$ has a fundamental system of solutions $Phi = Psi Phi_0$ where $Phi_0 = "exp"(B log)$ for a constant matrix $B$ and $Psi$ is invariant under deck transformations.

#definition[
    The origin is called a regular singular point of the equation $w' = A w$ if $Psi$ has at most a pole (not necessarily a simple pole) at the origin.
]

#lemma(id: "lm:gronwall")[
    Suppose $K >= 0$ is a constant and $F: (0, r_0] -> \R_+$ is a continuously partialerentiable function such that
    $
    |F'(r)| <= (K)/(r) F(r)
    $
    for every $0 < r <= r_0$, then
    $
    F(r) <= F(r_0) ((r)/(r_0))^(-K)
    $
    for every $0 < r <= r_0$.   
]

#proof[
        Write
        $
        & (d)/(d r) log F(r) = (F'(r))/(F(r)) >= -(K)/(r), \
        => & integral_r^(r_0) (d)/(d r) log F(r) d r >= -integral_r^(r_0) (K)/(r) d r, \
        => & log F(r_0) - log F(r) >= -K log r_0 + K log r, \
        => & log (F(r_0))/(F(r)) >= K log (r)/(r_0), \
        => & F(r) <= F(r_0) ((r)/(r_0))^(-K).
        $
     $qed$
]

#lemma(id: "lm:derivative")[
    If $f in cal(O)(X)$, then
    $
    abs((partial)/(partial r) |f|^2) <= 2 |f||f'|.
    $   
]

#proof[
        Note that $f' = d f/d z = 1/e^(i theta) (partial F)/partial r$, hence
        $
        abs((partial F)/(partial r)) = |e^(i theta) f'| = |f'|,
        $
        and
        $
        abs((partial overline(f))/(partial r)) = abs(overline((partial f)/(partial r))) = |f'|.
        $
        Hence
        $
        abs((partial)/(partial r) |f|^2) = abs((partial f)/(partial r) overline(f) + f (partial overline(f))/(partial r)) <= abs((partial f)/(partial r)) |overline(f)| + |f| abs((partial overline(f))/(partial r)) = 2 |f||f'|.
        $
     $qed$
]

#theorem[
    If $A$ has at most a pole of order 1 at the origin, then the origin is a regular singular point of the equation $w' = A w$.
    
]

#proof[
        Write $Phi = Psi Phi_0$ where $Phi_0 = "exp"(B log)$ and $Psi$ is invariant under deck transformations, then
        $
        Phi' = Psi' Phi_0 + Psi Phi_0' = Psi' Phi_0 + Psi (B)/(z) Phi_0,
        $
        and
        $
        Phi' = A Phi = A Psi Phi_0.
        $
        Apply $Phi_0^(-1)$ on the right, we get
        $
        Psi' + Psi (B)/(z) = A Psi.
        $
        By assumption, we can write $A = A_1/z$ for some $A_1 in M(n times n, B_R (0))$. Hence
        $
        Psi' = (1)/(z) (A_1 - B) Psi.
        $
        Define the matrix norm $\|M\| = (sum_(i, j) |M_(i j)|^2)^(1/2)$, then
        $
        \|Psi'\| <= (1)/(|z|) \|A_1 - B\| \|Psi\|.
        $
        If for all $0 < r_0 < R$, there exists integer $M >= 0$ such that for all $0 < r <= r_0$,
        $
        r^M \|Psi(r e^(i theta))\| <= r_0^M \|Psi(r_0 e^(i theta))\| < oo,
        $
        then $Psi$ has at most a pole of order $M$ at the origin. It remains to show that such an integer $M$ exists.

        Let $M = limits("max")_(|z| <= r_0) \|A_1(z) - B\|$, then
        $
        \|Psi'\| <= (M)/(r) \|Psi\|
        $
        for every $0 < r <= r_0$. Suppose $psi_(j k)$ are the entries of $Psi$. For fixed $theta$, let
        $
        F(r) = \|Psi(r e^(i theta))\|^2 = sum_(j, k) |psi_(j k)(r e^(i theta))|^2,
        $
        then by @lm:derivative,
        $
        |F'(r)| &= |( sum_(j, k )| (partial)/(partial r) |psi_(j k)(r e^(i theta))|^2) <= sum_(j, k) |((partial)/(partial r) |psi_(j k)(r e^(i theta))|^2) \
        &<= sum_(j, k) 2 |psi_(j k)(r e^(i theta))| |psi_(j k)'(r e^(i theta))| <= 2 \|Psi\| \|Psi'\| <= (2M)/(r) \|Psi\|^2 = (2M)/(r) F(r).
        $
        From @lm:gronwall, we have
        $
        F(r) <= F(r_0) ((r)/(r_0))^(-2M),
        $
        which implies that $r^M \|Psi(r e^(i theta))\| <= r_0^M \|Psi(r_0 e^(i theta))\| < oo$ for every $0 < r <= r_0$. Hence $Psi$ has at most a pole of order $M$ at the origin, which completes the proof.
     $qed$
]

#example[
    Let $X = B_R (0)^*$ and $a, b in cal(O)(B_R (0))$ and consider the equation
    $
    w'' + (a)/(z) w' + (b)/(z^2) w = 0
    $
    Set $w_1 = w$ and $w_2 = z w'$ and let $w = (w_1, w_2)^t$, then the above equation is equivalent to
    $
    d w = mat(
        0, -(b)/(z) ;
        (1)/(z), (1 - a)/(z)
    ) w.
    $
    On $p: tilde(X) -> X$, $Phi(z) = z^n psi(z) "exp"(B log)$. By a change of basis we may assume that $B$ is in Jordan normal form. In the first case,
    $
    B = mat(
        alpha_1, 0 ;
        0, alpha_2
    ) ~> "exp"(B log) = mat(
        z^(alpha_1), 0 ;
        0, z^(alpha_2)
    ),
    $
    hence
    $
    Phi(z) = mat(
        phi.alt_1(z), phi.alt_2(z) ;
        z phi.alt_1'(z), z phi.alt_2'(z)
    ) = z^n mat(
        psi_1(z), psi_2(z) ;
        psi_3(z), psi_4(z)
    ) mat(
        z^(alpha_1), 0 ;
        0, z^(alpha_2)
    ),
    $
    hence $phi.alt_1(z) = z^(n + alpha_1) psi_1(z)$ and $phi.alt_2(z) = z^(n + alpha_2) psi_2(z)$. In the second case,
    $
    B = mat(
        alpha, 1 ;
        0, alpha
    ) ~> "exp"(B log) = mat(
        z^(alpha), z^(alpha) log z ;
        0, z^(alpha)
    ),
    $
    hence
    $
    Phi(z) = mat(
        phi.alt_1(z), phi.alt_2(z) ;
        z phi.alt_1'(z), z phi.alt_2'(z)
    ) = z^n mat(
        psi_1(z), psi_2(z) ;
        psi_3(z), psi_4(z)
    ) mat(
        z^(alpha), z^(alpha) log z ;
        0, z^(alpha)
    ),
    $
    hence $phi.alt_1(z) = z^(n + alpha) psi_1(z)$ and $phi.alt_2(z) = z^(n + alpha) (psi_1(z) log z + psi_2(z))$.
]

#example[ [Bessel's equation]
    Consider the equation
    $
    w'' + (1)/(z) w' + (1 - (p^2)/(z^2)) w = 0
    $
    By the above theorem, it has at least one solution of the form
    $
    phi.alt(z) = z^rho sum_(n=0)^oo c_n z^n, quad  c_0 != 0.
    $
    then partialerentiating term by term we get
    $
    phi.alt'(z) = z^rho sum_(n=0)^oo (rho + n) c_n z^(n-1), \
    phi.alt''(z) = z^rho sum_(n=0)^oo (rho + n)(rho + n - 1) c_n z^(n-2).
    $
    Comparing the coefficients when $n = 0, 1, 2$, we get
    $
    (rho^2 - p^2) c_0 = 0, \
    ((rho + 1)^2 - p^2) c_1 = 0, \
    ((rho + n)^2 - p^2) c_n + c_(n-2) = 0 " for every " n >= 2.
    $
    Since $c_0 != 0$, we have $rho = plus.minus p$, so $(2rho + 1)c_1 = 0$ and for $n = 2k$,
    $
    4k(rho + k) c_(2k) + c_(2k-2) = 0.
    $
    If $p in CC without ZZ$, let $c_1 = 0$, $c_(2k+1) = 0$, then
    $
    c_(2k) = (-1)^k ((1)/(2))^(2k) (1)/(Gamma(k + 1) Gamma(rho + k + 1)),
    $
    define
    $
    J_p(z) = ((z)/(2))^p sum_(k=0)^oo ((-1)^k)/(Gamma(k + 1) Gamma(rho + k + 1)) ((z)/(2))^(2k),
    $
    which is called the Bessel function of order $rho$. If $p in.not ZZ$ then $J_p$ and $J_(-p)$ are linearly independent, hence they form a fundamental system of solutions. If $p in ZZ$, then $J_p$ and $J_(-p)$ are linearly dependent, hence we need to find another solution. Let
    $
    psi(z) = J_p(z) log z + g(z),
    $
    where $g$ is a holomorphic function on $X$ to be determined. Then
    $
    psi'(z) = J_p'(z) log z + (J_p(z))/(z) + g'(z), \
    psi''(z) = J_p''(z) log z + (2 J_p'(z))/(z) - (J_p(z))/(z^2) + g''(z).
    $
    Substitute into the equation, we get
    $
    g''(z) + (1)/(z) g'(z) + (1 - (p^2)/(z^2)) g(z) = -(2)/(z) J_p'(z).
    $
    The equation can be solved by a power series of the form
    $
    g(z) = z^(-p) sum_(n=0)^oo a_n z^n.
    $
]

= Compact Riemann Surfaces

== Vanishing Theorems

Let $X$ be a differential manifold, and $frak(U) = (U_i)_(i in I)$ be an open cover of $X$. A family $(g_i)_(i in I)$ of functions $g_i: X -> RR$ is called a partition of unity subordinate to $frak(U)$ if

    + $0 <= g_i(x) <= 1$ for every $i in I$ and $x in X$;
    + $"supp" g_i subset U_i$ for every $i in I$;
    + for every $x in X$, there exists a neighborhood $V$ of $x$ such that $g_i|_V = 0$ for all but finitely many $i in I$, and $sum_(i in I) g_i(x) = 1$ for every $x in X$.


#theorem[
    If $X$ is a differential manifold, with a countable basis, then for every open cover $frak(U)$ of $X$, there exists a partition of unity subordinate to $frak(U)$.
]

#lemma[
    Let $A subset X$ be clased and $A subset U$ for some open set $U$, then there exists a function infinitely partialerentiable $phi.alt: X -> RR$ such that $0 <= phi.alt(x) <= 1$ for every $x in X$, $phi.alt|_A = 1$ and $phi.alt|_(X without U) = 0$.
    
]

#proof[
        Since $\{ U, X without A \}$ is an open cover of $X$, there exists a partition of unity $(g_1, g_2)$ subordinate to $\{ U, X without A \}$, then we can take $phi.alt = g_1$.
     $qed$
]

Let $X$ be a Riemann surface, $frak(U) = (U_i)_(i in I)$ an open cover of $X$ and $cal(F)$ a sheaf of abelian groups on $X$. Let $cal(O), cal(E), cal(E)^((1))$ denote the sheaves of holomorphic functions, infinitely partialerentiable functions and infinitely partialerentiable 1-forms on $X$ respectively.$CC, ZZ, QQ, RR$ denote the locally constant sheaves with stalks $CC, ZZ, QQ, RR$ respectively.

Define the $0$-th, $1$-st and $2$-nd cochain groups by
$
    C^0(frak(U), cal(F)) = product_(i in I) cal(F)(U_i), \
    C^1(frak(U), cal(F)) = product_(i, j in I) cal(F)(U_i inter U_j), \
    C^2(frak(U), cal(F)) = product_(i, j, k in I) cal(F)(U_i inter U_j inter U_k).
$
Define the coboundary operators by
$
    delta: C^0(frak(U), cal(F)) &-> C^1(frak(U), cal(F)), quad  (f_i)_(i in I) |-> (f_i - f_j)_(i, j in I), \
    delta: C^1(frak(U), cal(F)) &-> C^2(frak(U), cal(F)), quad  (f_(i j))_(i, j in I) |-> (f_(i j) - f_(i k) + f_(j k))_(i, j, k in I).
$
We can easily verify that $delta^2 = 0$, hence we can define the $0$-th and $1$-st cohomology groups by
$
    Z^0(frak(U), cal(F)) = "ker" delta: C^0(frak(U), cal(F)) -> C^1(frak(U), cal(F)) tilde.equiv cal(F)(X), \
    B^0(frak(U), cal(F)) = "Im" delta: C^(-1)(frak(U), cal(F)) -> C^0(frak(U), cal(F)) = 0, \
    H^0(frak(U), cal(F)) = Z^0(frak(U), cal(F)) \/ B^0(frak(U), cal(F)) tilde.equiv cal(F)(X),
$
and
$
    Z^1(frak(U), cal(F)) = "ker" delta: C^1(frak(U), cal(F)) -> C^2(frak(U), cal(F)), \
    B^1(frak(U), cal(F)) = "Im" delta: C^0(frak(U), cal(F)) -> C^1(frak(U), cal(F)), \
    H^1(frak(U), cal(F)) = Z^1(frak(U), cal(F)) / B^1(frak(U), cal(F)).
$
The elements in $Z^1(frak(U), cal(F))$ are called 1-cocycles and the elements in $B^1(frak(U), cal(F))$ are called 1-coboundaries. Concretely, a 1-cocycle is a family $(f_(i j))_(i, j in I)$ of sections $f_(i j) in cal(F)(U_i inter U_j)$ such that
$
f_(i j) - f_(i k) + f_(j k) = 0
$
for every $i, j, k in I$, and a 1-coboundary is a family $(f_(i j))_(i, j in I)$ of sections $f_(i j) in cal(F)(U_i inter U_j)$ such that there exists a 0-cochain $(g_i)_(i in I)$ of sections $g_i in cal(F)(U_i)$ such that
$
f_(i j) = g_i - g_j
$
for every $i, j in I$.

However, the above definition of cohomology groups depends on the choice of open cover $frak(U)$. We define a direct partial order on the set of open covers of $X$ by $frak(V) = (V_k)_(k in K) < frak(U) = (U_i)_(i in I)$ if there exists an assignment $tau: K -> I$ such that $V_k subset U_(tau(k))$ for every $k in K$. For any two covering $frak(V)' = (V_k')_(k in K')$ and $frak(V)'' = (V_k'')_(k in K'')$, we can take
$
frak(V) = (V_k' inter V_(k'')'')_((k', k'') in K' times K'') < frak(V)', frak(V)'',
$
then $frak(V) < frak(V)', frak(V)''$. This gives a directed system of cohomology groups $\{ H^1(frak(U), cal(F)) \}_(frak(U))$: if $frak(V) < frak(U)$, then there exists a homomorphism
$
t_(frak(V))^(frak(U)): H^1(frak(U), cal(F)) -> H^1(frak(U), cal(F)), quad  f_(k l) |-> f_(tau(k) tau(l))|_(V_k inter V_l).
$
Note that $t_(frak(V))^(frak(U))$ is independent of the choice of $tau$: if $tau': K -> I$ is another assignment such that $V_k subset U_(tau'(k))$ for every $k in K$, then
$
f_(tau(k) tau(l)) - f_(tau'(k) tau'(l)) &= (f_(tau(k) tau(l)) + f_(tau(l) tau'(k))) - (f_(tau(l) tau'(k)) - f_(tau'(k) tau'(l))) \
&= f_(tau(k) tau'(k)) - f_(tau(l) tau'(l)),
$
thus we can define that $h_k = f_(tau(k) tau'(k))$ for every $k in K$, then $h_k$ is a 0-cochain hence $f_(tau(k) tau(l)) - f_(tau'(k) tau'(l)) = h_k - h_l in B^1(frak(V), cal(F))$, which implies that $f_(tau(k) tau(l))$ and $f_(tau'(k) tau'(l))$ represent the same element in $H^1(frak(V), cal(F))$, hence $t_(frak(V))^(frak(U))$ is independent of the choice of $tau$.

Suppose that $(f_(tau(k) tau(l)))_(k, l in K)$ is a 1-coboundary, then there exists a 0-cochain $(g_k)_(k in K)$ such that $f_(tau(k) tau(l)) = g_k - g_l$ for every $k, l in K$. Note that $(U_i inter V_k)_(k in K)$ is an open cover of $U_i$. On $U_i inter V_k inter V_l$, we have
$
g_k - g_l = f_(tau(k) tau(l)) = f_(tau(k) i) + f_(i tau(l)) ~> g_k + f_(i tau(k)) = g_l + f_(i tau(l)).
$
By sheaf axiom, there exists a section $h_i in cal(F)(U_i)$ such that $h_i|_(U_i inter V_k) = g_k + f_(i tau(k))$ for every $k in K$. Then for every $i, j in I$ and $k in K$, we have
$
f_(i j) = f_(i tau(k)) - f_(j tau(k)) = (h_i - g_k) - (h_j - g_k) = h_i - h_j,
$
hence $(f_(i j))_(i, j in I)$ is a 1-coboundary, which implies that $t_(frak(V))^(frak(U))$ is injective.

If $frak(W) < frak(V) < frak(U)$, then $t_(frak(W))^(frak(U)) = t_(frak(W))^(frak(V)) compose t_(frak(V))^(frak(U))$, hence $\{ H^1(frak(U), cal(F)) \}_(frak(U))$ is a directed system of abelian groups. Define the first cohomology group of $X$ with coefficients in $cal(F)$ by
$
H^1(X, cal(F)) = varinjlim_(frak(U)) H^1(frak(U), cal(F)) = product.co_(frak(U)) H^1(frak(U), cal(F)) \/ tilde.op,
$
where $tilde.op$ is the equivalence relation defined by $xi tilde.op xi'$ if $xi in H^1(frak(U), cal(F))$, $xi' in H^1(frak(U)', cal(F))$ and there exists a common refinement $frak(V) < frak(U), frak(U)'$ such that $t_(frak(V))^(frak(U))(xi) = t_(frak(V))^(frak(U)')(xi')$. Addition can be defined by $xi + xi' = t_(frak(V))^(frak(U))(xi) + t_(frak(V))^(frak(U)')(xi')$ for some common refinement $frak(V) < frak(U), frak(U)'$, which is well-defined and makes $H^1(X, cal(F))$ an abelian group. The natural embedding $H^1(frak(U), cal(F)) -> H^1(X, cal(F))$ is injective for every open cover $frak(U)$, in particular $H^1(X, cal(F)) = 0$ if and only if $H^1(frak(U), cal(F)) = 0$ for all open cover $frak(U)$.

#theorem(name: "Dolbeault's lemma")[ 
    Suppose $X = B_R (0)$ with $0 < R <= oo$ and $g in cal(E)(X)$, then there exists $f in cal(E)(X)$ such that $(partial F)/partial overline(z) = g$.
]

#proof[
    We first assume that $g$ has compact support and $X = CC$. For $zeta in CC$, define
    $
    f(zeta) = (1)/(2pi i) integral.double_(CC) (g(z))/(z - zeta) d z and d overline(z).
    $
    Fix $zeta in CC$, and let $z = zeta + r e^(i theta)$, then $d z and d overline(z) = -2 i r d r and d theta$. Since $g$ has compact support, there exists $r_0 > 0$ such that $g(z) = 0$ for every $r >= r_0$. Hence
    $
    f(zeta) = (1)/(2pi i) integral.double_(0 <= r <= r_0) (g(zeta + r e^(i theta)))/(r e^(i theta)) (-2 i r) d r and d theta = -(1)/(pi) integral.double_(0 <= r <= r_0) g(zeta + r e^(i theta)) e^(-i theta) d r and d theta.
    $
    Since $g$ is infinitely partialerentiable, we can partialerentiate under the integral sign and get
    $
        ((partial F))/(partial overline(zeta)) &= -(1)/(pi) integral.double_(0 <= r <= r_0) (partial g)/(partial overline(zeta)) (zeta + r e^(i theta)) e^(-i theta) d r and d theta \
        &= (1)/(2pi i) lim_(epsilon -> 0) integral.double_(epsilon <= |z - zeta| <= r_0) (partial g)/(partial overline(z)) (z) (1)/(z - zeta) d z and d overline(z).
    $
    Let
    $
    w(z) = (1)/(2pi i) (g(z))/(z - zeta) d z ~> d w = (1)/(2pi i) (partial g)/(partial overline(z)) (1)/(z - zeta) d overline(z) and d z,
    $
    then by Stokes' theorem,
    $
    lim_(epsilon -> 0) integral.double_(epsilon <= |z - zeta| <= r_0) (partial g)/(partial overline(z)) (1)/(z - zeta) d z and d overline(z) = & -lim_(epsilon -> 0) integral.double_(epsilon <= |z - zeta| <= r_0) d w \
    = & -lim_(epsilon -> 0) integral_(|z - zeta| = r_0) w + lim_(epsilon -> 0) integral_(|z - zeta| = epsilon) w \
    = & 0 + lim_(epsilon -> 0) (1)/(2pi) integral_0^(2pi) g(zeta + epsilon e^(i theta)) d theta = g(zeta).
    $

    For general $g$, let $0 < R_0 < R_1 < dots$ such that $lim_(n -> oo) R_n = R$ and let $psi_n in cal(E)(X)$ such that $"supp" (psi_n) subset B_(R_(n+1))(0)$ and $psi_n|_(B_(R_n)(0)) = 1$ for every $n >= 0$. Define $g_n = psi_n g$, then $g_n$ has compact support, hence there exists $f_n in cal(E)(X)$ such that $overline(partial) f_n = partial f_n/partial overline(z) = g_n$.

    Let $\|f\|_K = sup_(z in K) |f(z)|$ be the supremum norm. Set $tilde(f)_1 = f_1$. Since $overline(partial) (f_2 - tilde(f)_1) = g_2 - g_1 = 0$ on $B_(R_1)(0)$, $f_2 - tilde(f)_1$ is holomorphic on $B_(R_1)(0)$, hence there exists a Taylor polynomial $P_1$ of $f_2 - tilde(f)_1$ at the origin such that $\|f_2 - tilde(f)_1 - P_1\|_(B_(R_0)(0)) < 1/2$. Define $tilde(f)_2 = f_2 - P_1$, then $\|tilde(f)_2 - tilde(f)_1\|_(B_(R_0)(0)) < 1/2$. Inductively, we can define $tilde(f)_n$ such that $\|tilde(f)_(n+1) - tilde(f)_n\|_(B_(R_(n-1))(0)) < 1/2^n$ and $overline(partial) tilde(f)_n = g_n$ for every $n >= 1$. Let $f = lim_(n -> oo) tilde(f)_n$. On $B_(R_n)(0)$, we may write
    $
    f = tilde(f)_n + sum_(k = n)^oo (f_(k+1) - tilde(f)_k),
    $
    since $tilde(f)_(k+1) - tilde(f)_k in cal(O)(B_(R_(n-1))(0))$ and $\|f_(k+1) - tilde(f)_k\|_(B_(R_n)(0)) < 1/2^k$ for every $k >= n$, the above series converges uniformly on $B_(R_n)(0)$, hence $f$ is infinitely partialerentiable on $X$. Moreover, $overline(partial) f = overline(partial) tilde(f)_n = g_n$ on $B_(R_n)(0)$ for every $n >= 1$, hence $overline(partial) f = g$ on $X$, which completes the proof.
    $qed$
]

#theorem[
    If $X$ is a Riemann surface, then $H^1(X, cal(E)) = 0$.
    
]

#proof[
        Given $frak(U) = (U_i)_(i in I)$, exists a partition of unity $(psi_i)_(i in I)$ subordinate to $frak(U)$. Let $(f_(i j))_(i, j in I)$ be a 1-cocycle of $cal(E)$ with respect to $frak(U)$, then for every $i, j in I$, we have
        $
        f_(i j) = sum_(k in I) psi_k f_(i j) = sum_(k in I) psi_k (f_(i k) - f_(j k)) = sum_(k in I) psi_k f_(i k) - sum_(k in I) psi_k f_(j k) = g_i - g_j,
        $
        where $g_i = sum_(k in I) psi_k f_(i k)$ for every $i in I$. Hence $(f_(i j))_(i, j in I)$ is a 1-coboundary, which implies that $H^1(frak(U), cal(E)) = 0$ for every open cover $frak(U)$, hence $H^1(X, cal(E)) = 0$.
     $qed$
]

#theorem[
    If $X$ is a simply connected Riemann surface, then $H^1(X, CC) = 0$.
    
]

#proof[
        For $frak(U) = (U_i)_(i in I)$ and $(c_(i j)) in Z^1(frak(U), CC) subset.eq Z^1(frak(U), cal(E))$, since $H^1(X, cal(E)) = 0$, there exists a 0-cochain $(f_i)_(i in I)$ of $cal(E)$ such that $c_(i j) = f_i - f_j$ for every $i, j in I$. Note that $0 = d c_(i j) = d f_i - d f_j$ for every $i, j in I$, hence there exists a 1-form $omega$ on $X$ such that $omega|_(U_i) = d f_i$ for every $i in I$. Note that $d omega|_(U_i) = d d f_i = 0$ for every $i in I$, hence $d omega = 0$ on $X$. Since $X$ is simply connected, there exists a function $f$ on $X$ such that $d f = omega$, hence $d f|_(U_i) = d f_i$ for every $i in I$, which implies that $c_i := f_i - f$ is a constant function on $U_i$ for every $i in I$. Hence for every $i, j in I$, we have
        $
        c_(i j) = f_i - f_j = (f_i - f) - (f_j - f) = c_i - c_j,
        $
        which implies that $(c_(i j))_(i, j in I)$ is a 1-coboundary, hence $H^1(frak(U), CC) = 0$ for every open cover $frak(U)$, hence $H^1(X, CC) = 0$.
     $qed$
]

#theorem[
    If $X$ is a simply connected Riemann surface, then $H^1(X, ZZ) = 0$.
    
]

#proof[
        For $frak(U) = (U_i)_(i in I)$ and $(a_(j k)) in Z^1(frak(U), ZZ) subset.eq Z^1(frak(U), CC)$, since $H^1(X, CC) = 0$, there exists a 0-cochain $(c_j)_(j in I)$ of $CC$ such that $a_(j k) = c_j - c_k$ for every $j, k in I$. Note that
        $
        1 = e^(2pi i a_(j k)) = e^(2pi i (c_j - c_k))  ~> e^(2pi i c_j) = e^(2pi i c_k)
        $
        for every $j, k in I$. Since $X$ is connected, there exists a constant $b in CC^*$ such that $e^(2pi i c_j) = b$ for every $j in I$. Let $b = e^(2pi i c)$ for some $c in CC$, then $e^(2pi i (c_j - c)) = 1$ for every $j in I$, hence $a_j := c_j - c$ is an integer for every $j in I$. Hence for every $j, k in I$, we have
        $
        a_(j k) = c_j - c_k = (c_j - c) - (c_k - c) = a_j - a_k,
        $
        which implies that $(a_(j k))_(j, k in I)$ is a 1-coboundary, hence $H^1(frak(U), ZZ) = 0$ for every open cover $frak(U)$, hence $H^1(X, ZZ) = 0$.
     $qed$
]

#theorem[
    Let $X = B_R (0)$ with $0 < R <= oo$, then $H^1(X, cal(O)) = 0$.
    
]

#proof[
        For $frak(U) = (U_i)_(i in I)$ and $(f_(i j)) in Z^1(frak(U), cal(O)) subset.eq Z^1(frak(U), cal(E))$, since $H^1(X, cal(E)) = 0$, there exists a 0-cochain $(f_i)_(i in I)$ of $cal(E)$ such that $f_(i j) = f_i - f_j$ for every $i, j in I$. Note that
        $
        0 = overline(partial) f_(i j) = overline(partial) f_i - overline(partial) f_j ~> overline(partial) f_i = overline(partial) f_j
        $
        for every $i, j in I$, hence there exists a function $h in cal(E)(X)$ such that $h|_(U_i) = overline(partial) f_i$ for every $i in I$. By Dolbeault's lemma, there exists a function $g in cal(E)(X)$ such that $overline(partial) g = h$, hence $overline(partial) (f_i - g) = 0$ for every $i in I$, which implies that $f_i - g$ is holomorphic on $U_i$ for every $i in I$. Hence for every $i, j in I$, we have
        $
        f_(i j) = f_i - f_j = (f_i - g) - (f_j - g),
        $
        which implies that $(f_(i j))_(i, j in I)$ is a 1-coboundary, hence $H^1(frak(U), cal(O)) = 0$ for every open cover $frak(U)$, hence $H^1(X, cal(O)) = 0$.
     $qed$
]

#theorem(name: "Leray's theorem")[ 
    Let $X$ be a Riemann surface and $cal(F)$ a sheaf of abelian groups on $X$. If there exists an open cover $frak(U)$ of $X$ such that $H^1(U_i, cal(F)) = 0$ for every $i in I$, then $H^1(X, cal(F)) tilde.equiv H^1(frak(U), cal(F))$.
    
]

#proof[
        It suffices to show that for all refinements $frak(V) < frak(U)$, the homomorphism $t_(frak(V))^(frak(U)): H^1(frak(U), cal(F)) -> H^1(frak(V), cal(F))$ is an isomorphism. We've alread y shown that $t_(frak(V))^(frak(U))$ is injective.

        Let $tau: K -> I$ be an assignment such that $V_k subset U_(tau(k))$ for every $k in K$. Fix $(f_(k l)) in Z^1(frak(V), cal(F))$. By assumption, $H^1(U_i inter frak(V), cal(F)) = 0$ for every $i in I$, hence there exists a 0-cochain $(g_(i k))_(k in K)$ of $cal(F)$ such that $f_(k l) = g_(i k) - g_(i l)$ for every $k, l in K$. On $U_i inter U_j inter V_k inter V_l$, we have
        $
        f_(k l) = g_(i k) - g_(i l) = g_(j k) - g_(j l) ~> g_(j k) - g_(i k) = g_(j l) - g_(i l),
        $
        hence there exists a section $F_(i j) in cal(F)(U_i inter U_j)$ such that $F_(i j) = g_(j k) - g_(i k)$ for every $k in K$. Then for every $i, j in I$ and $k in K$, we have
        $
        F_(i j) + F_(j t) = g_(i k) - g_(j k) + g_(j k) - g_(t k) = g_(i k) - g_(t k) = F_(i t),
        $
        which implies that $(F_(i j))_(i, j in I)$ is a 1-cocycle of $cal(F)$ with respect to $frak(U)$. On $V_k inter V_l$, we have
        $
        F_(tau(k) tau(l)) - f_(k l) = (g_(tau(l) k) - g_(tau(k) k)) - (g_(tau(l) k) - g_(tau(l) l)) = g_(tau(l) l) - g_(tau(k) k),
        $
        which implies that $t_(frak(V))^(frak(U))([F_(i j)]) = [f_(k l)]$, hence $t_(frak(V))^(frak(U))$ is surjective, which completes the proof.
     $qed$
]

== Finiteness Theorems

Write $Y_1 subset.double Y_2$ if $overline(Y_1)$ is a compact subset of $Y_2$.

#theorem(name: "Finiteness theorem")[ 
    Let $X$ be a Riemann surface and $Y_1 subset.double Y_2 subset X$ be open subsets of $X$, then the restriction map $H^1(Y_2, cal(O)) -> H^1(Y_1, cal(O))$ has a finite-dimensional image. In particular, if $X$ is compact, then $H^1(X, cal(O))$ is finite-dimensional.
    
]

#proof[
        We choose finitely many charts $\{ (U_i, z_i) \}_(i = 1, dots.h, n)$ and relatively compact subsets $W_i subset.double V_i subset.double U_i subset.double U_i'$ such that
        
        + $Y_1 subset union.big_(i = 1)^n W_i =: Y' subset.double Y'' := union.big_(i = 1)^n U_i subset Y_2$;
        + $z_i(W_i), z_i(U_i), z_i(U_i')$ are disks in $CC$. 
        
        Let $frak(U)' = (U_i')$, $frak(U) = (U_i)$ and $frak(W) = (W_i)$, then by the key proposition (to be proved later), there exists a finite-dimensional subspace $S subset Z^1(frak(U), cal(O))$ such that for all $xi in Z^1(frak(U), cal(O))$, there exists $sigma in S$, $eta in C^0(frak(W), cal(O))$ such that $sigma = xi + delta eta$ on $frak(W)$. Hence the image of $H^1(frak(U), cal(O)) -> H^1(frak(W), cal(O))$ is finite-dimensional (equals to the image of $S$). Since $H^1(frak(U)_i, cal(O)) = 0$ and $H^1(frak(W)_i, cal(O)) = 0$ for every $i$, by Leray's theorem, 
        $
        H^1(U, cal(O)) tilde.equiv H^1(Y'', cal(O)), quad  H^1(W, cal(O)) tilde.equiv H^1(Y', cal(O)). 
        $
        Since the restriction map $H^1(Y_2, cal(O)) -> H^1(Y_1, cal(O))$ factors through $H^1(Y'', cal(O)) -> H^1(Y', cal(O))$, the image of $H^1(Y_2, cal(O)) -> H^1(Y_1, cal(O))$ is finite-dimensional. In particular, if $X$ is compact, then $H^1(X, cal(O))$ is finite-dimensional.
     $qed$
]

#definition[
    Let $X$ be a Riemann surface, then the genus of $X$ is defined by
    $
    g(X) = dim H^1(X, cal(O)).
    $
]

#lemma[
    Let $X$ be a Riemann surface and $Y subset.double X$, $a in Y$, then exists a meromorphic function $f in cal(M)(Y)$ such that $f$ has a pole at $a$ and $f in cal(O)(Y without \{ a \})$.
    
]

#proof[
        Let $(U_1, z)$ be a coordinate neighborhood of $a$ such that $z(a) = 0$. Set $U_2 = X without \{ a \}$, then $frak(U) = (U_1, U_2)$ is an open cover of $X$. By the finiteness theorem, 
        $
        k := dim "Im" (H^1(cal X, cal(O)) -> H^1(cal Y, cal(O))) < oo. 
        $
        Since $H^1(frak(U), cal(O)) arrow.r.hook H^1(cal X, cal(O))$ and $H^1(frak(U) inter Y, cal(O)) arrow.r.hook H^1(cal Y, cal(O))$ are injective, we have
        $
        dim "Im" (H^1(frak(U), cal(O)) -> H^1(frak(U) inter Y, cal(O))) <= k.
        $
        Observe that $z^(-j) in cal(O)(U_1 inter U_2)$ for every $j = 1, dots.h, k+1$, so let $xi_j = overline(z^(-j)) in H^1(frak(U), cal(O))$, then $xi_1, dots.h, xi_(k+1)$ are linearly dependent in $H^1(frak(U) inter Y, cal(O))$, hence there exists $c_1, dots.h, c_(k+1) in CC$, not all zero and $f_1 in cal(O)(U_1 inter Y)$, $f_2 in cal(O)(U_2 inter Y)$ such that
        $
        sum_(j = 1)^(k+1) c_j z^(-j) = f_2 - f_1 quad  "on " U_1 inter U_2 inter Y.
        $
        Let $f$ be the meromorphic function on $Y$ defined by $f|_(U_1 inter Y) = f_1 + sum_(j = 1)^(k+1) c_j z^(-j)$ and $f|_(U_2 inter Y) = f_2$, then $f$ has a pole at $a$ and $f in cal(O)(Y without \{ a \})$, which completes the proof.
     $qed$
]

#lemma[
    Let $X$ be a non-compact Riemann surface and $Y subset.double X$, then there exists a non-constant holomorphic function on $Y$.
    
]

#proof[
        Since $X$ is non-compact, there exists $Y_1$ such that $Y subset.double Y_1 subset.double X$. Pick $a in Y_1 without Y$, then by the previous corollary, there exists $f_1 in cal(O)(Y_1 without \{ a \})$ such that $f_1$ has a pole at $a$. Let $f$ be the holomorphic function on $Y$ defined by $f = f_1|_Y$, then $f$ is non-constant, which completes the proof.
     $qed$
]

On a open subset $frak(U)$, we can always write a 1-form $omega in cal(E)^1(frak(U))$ locally as $omega = f d x + g d y = phi.alt d z + psi d overline(z)$, where $d z = d x + i d y$ and $d overline(z) = d x - i d y$. In this case, we say $phi.alt d z in cal(E)^(1, 0)(frak(U))$ is the $(1, 0)$-part of $omega$ and $psi d overline(z) in cal(E)^(0, 1)(frak(U))$ is the $(0, 1)$-part of $omega$. We can also write
$
d f = ((partial F))/(partial z) d z + ((partial F))/(partial overline(z)) d overline(z)
$
for every $f in cal(E)(frak(U))$, then $(partial F)/partial z d z$ is the $(1, 0)$-part of $d f$ and $(partial F)/partial overline(z) d overline(z)$ is the $(0, 1)$-part of $d f$. We denote $(partial F)/partial z d z$ by $d' f$ and $(partial F)/partial overline(z) d overline(z)$ by $d'' f$, then we have $d f = d' f + d'' f$. Note that $d'^2 = 0$, $d''^2 = 0$. 

#theorem(id: "thm:general_dolbeault_i", name: "General form (I) for Dolbeault's lemma")[ 
    Let $X$ be a non-compact Riemann surface and $Y subset.double Y' subset.double X$, $omega in cal(E)^(0, 1)(Y')$ , then there exists $g in cal(E)(Y)$ such that $d'' g = omega$ on $Y$.
    
]

#proof[
        By Dolbeault's lemma, exists $frak(U) = (U_i)_(i in I)$ such that each $U_i$ is isomorphic to a disk and $omega|_(U_i) = d'' f_i$ for some $f_i in cal(E)(U_i)$ for every $i in I$ (Since we can write $omega = phi.alt d overline(z)$, and by Dolbeault's lemma, there exists $f_i$ such that $partial f_i/partial overline(z) = phi.alt$ on $U_i$). 

        Note that
        $
        d'' (f_i - f_j) = 0 ~> f_i - f_j in cal(O)(U_i inter U_j) ~> (f_i - f_j)_(i, j in I) in Z^1(frak(U), cal(O)).
        $
        If we can prove that $L := "Im" (H^1(Y', cal(O)) -> H^1(Y, cal(O))) = 0$, then there exists a 0-cochain $(g_i)_(i in I)$ of $cal(O)$ such that $f_i - f_j = g_i - g_j$ for every $i, j in I$, hence $f_i - g_i = f_j - g_j$ on $U_i inter U_j inter Y$ for every $i, j in I$, which implies that there exists a function $g$ on $Y$ such that $g|_(U_i inter Y) = f_i - g_i$ for every $i in I$, hence $d'' g = d'' f_i = omega$ on $Y$, which completes the proof.

        We now prove that $L = 0$. Let $xi_1, dots.h, xi_n in H^1(Y', cal(O))$ such that $xi_1|_Y, dots.h, xi_n|_Y$ is a basis of $L$. Let $f in cal(O)(Y')$ be a non-constant holomorphic function. Since $f xi_i in H^1(Y', cal(O))$ for every $i$, we can write $f xi_i|_Y = sum_(j = 1)^n c_(i j) xi_j|_Y$ for some $c_(i j) in CC$. Using the determinant trick, we have $F := "det" (c_(i j) - f delta_(i j)) in cal(O)(Y')$ and $F xi_i|_Y = 0$ for every $i$, hence $F xi|_Y = 0$ for every $xi in L$. We can pick a covering $frak(V) = (V_i)_(i in I)$ of $Y$ such that each zero is contained in a single $V_i$, then $F|_(V_i inter V_j)$ contains no zero, hence there exists $g_(i j) := (F|_(V_i inter V_j))^(-1)f_(i j)$, i.e. $f_(i j) = F g_(i j)$ for every $i, j in I$. Let $zeta, xi in H^1(frak(V), cal(O))$ be the classes of $(f_(i j)), (g_(i j))$ respectively, then $zeta = F xi$ and $zeta|_Y = F xi|_Y = 0$, hence proved that $L = 0$.
     $qed$
]

== Proof of Finiteness by $L^2$-norm Estimates

Recall that
$
\|f\|_(L^2(D)) := ( integral.double_D |f(x + i y)|^2 d x d y )^(1/2) in \R_(>= 0) union \{ oo \} \ 
L^2(D, cal(O)) := \{ f in cal(O)(D): \|f\|_(L^2(D)) < oo \}.
$
We have
$
\|f\|_(L^2(D)) <= sqrt(pi) R \|f\|_(L^oo(D)), 
$
where $\|f\|_(L^oo(D)) = sup_(z in D) |f(z)|$. If $f, g in L^2(D, cal(O))$, then write their inner product as
$
chevron.l f, g chevron.r_(L^2(D)) := integral.double_D f(z) overline(g(z)) d x d y, 
$
then $L^2(D, cal(O))$ is a Hilbert space with respect to $chevron.l dot, dot chevron.r_(L^2(D))$. For $B = B_r(a)$, the family of functions
$
psi_n(z) = (z-a)^n, quad  n = 0, 1, 2, dots.h
$
forms an orthogonal basis of $L^2(B, cal(O))$. We can verify that
$
chevron.l psi_n, psi_m chevron.r_(L^2(B)) & = integral.double_B (z-a)^n overline((z-a)^m) d x d y \
& = integral.double_(0 <= theta < 2pi, 0 <= rho < r) rho^(n+m) e^(i(n-m)theta) rho d rho d theta = cases(
    0 & "if" n != m,
    (pi r^(2n+2))/(n+1) & "otherwise",
)
$
Therefore, $\|psi_n\|_(L^2(B)) = sqrt(pi) r^(n+1)/sqrt(n+1)$ for every $n$. For all $a in B_rho(0)$, we can write $f(z) = sum_(n = 0)^oo c_n (z-a)^n$ for every $f in L^2(B, cal(O))$, then
$
|f(a)| = |c_0| <= (1)/(sqrt(pi) r) \|f\|_(L^2(B)) <= (1)/(sqrt(pi) (r - rho)) \|f\|_(L^2(B_rho(0), cal(O))).
$

#definition[
    Let $X$ be a Riemann surface and $cal(U)' = (U_i', z_i)_(i = 1, dots.h, n)$ be a family of charts such that $z_i(U_i')$ is a disk in $CC$ for every $i$. Suppose $U_i subset U_i'$ and $cal(U) = (U_i)_(i = 1, dots.h, n)$ is an open cover of $X$. For $eta = (f_i) in C^0(cal(U), cal(O))$, we define
    $
    \|eta\|_(L^2(cal(U)))^2 := sum_(i = 1)^n \|eta_i\|_(L^2(U_i))^2.
    $
    For $xi = (f_(i j)) in C^1(cal(U), cal(O))$, we define
    $
    \|xi\|_(L^2(cal(U)))^2 := sum_(i, j) \|f_(i j)\|_(L^2(U_i inter U_j))^2.
    $
    Let $C_(L^2)^0(cal(U), cal(O))$ be the set of $0$-cochains having finite $L^2$-norm and $C_(L^2)^1(cal(U), cal(O))$ be the set of $1$-cochains having finite $L^2$-norm, then these spaces are Hilbert spaces since $\|f\|_(D_r) <= (1)/(sqrt(pi) r) \|f\|_(L^2(D_r))$ so the convergence in $L^2$-norm implies the convergence in $L^oo$-norm, i.e. converge uniformly on compact subsets.
]

#proposition[
    Let $cal(U) = (U_i)_(i = 1, dots.h, n)$ and $cal B = (V_i)_(i = 1, dots.h, n)$ be two open covers of $X$ such that $V_i subset.double U_i$ for every $i$. Then for all $xi in C^1(cal(U), cal(O))$, 
    
        + $\|xi\|_(L^2(cal B)) < oo$;
        + for all $epsilon > 0$, there exists a finite codimensional subspace $A subset Z_(L^2)^1(cal(U), cal(O))$ such that for all $xi in A$, 
        $
        \|xi\|_(L^2(cal B)) < epsilon \|xi\|_(L^2(cal(U))).
        $
    
    
]

#proof[
        
            + 	 Since $f_(i j)$ is bounded on $overline(V_i inter V_j)$ for every $i, j$, we have $\|f_(i j)\|_(L^2(V_i inter V_j)) < oo$ for every $i, j$, hence $\|xi\|_(L^2(cal B)) < oo$.
            + 	 We need a finite codimensional $A$ such that
            $
            \|f_(i j)\|_(L^2(V_i inter V_j)) < epsilon \|f_(i j)\|_(L^2(U_i inter U_j))
            $
            for every $i, j$ and $xi = (f_(i j)) in A$. Fix a pair of $i, j$ and let $V = V_i inter V_j$, $U = U_i inter U_j$, $f = f_(i j)$. 

            Since $overline(V)$ is compact, exists $r$ and $a_1, dots.h, a_k in U$ such that $overline(B_r(a_j)) subset U$ for every $j$ and $V subset union.big_(j = 1)^k B_(r/2)(a_j)$. Pick $n >> 0$ such that $2^(-n-1) k <= epsilon$. Let
            $
            A = \{ f in L^2(U, cal(O)) | f(z) = sum_(i=n \}^oo c_(i j) (z - a_j)^i " for every " j = 1, dots.h, k).
            $
            Then $A$ has codimension at most $k n$ in $L^2(U, cal(O))$ (forcing zeros of order at least $n$ at $a_j$ for every $j$). For $rho <= r$, we have
            $
            \|f\|_(L^2(B_rho(a_j)))^2 = sum_(i = n)^oo |c_(i j)|^2 \|psi_i\|_(L^2(B_rho(a_j)))^2 = sum_(i = n)^oo (pi rho^(2i+2))/(i+1) |c_(i j)|^2, 
            $
            in particular
            $
            \|f\|_(L^2(B_(r/2)(a_j)))^2 = sum_(i = n)^oo (pi r^(2i+2))/(i+1) (1)/(2^(2i+2)) |c_(i j)|^2 <= (1)/(2^(2n+2)) sum_(i = n)^oo (pi r^(2i+2))/(i+1) |c_(i j)|^2 = (1)/(2^(2n+2)) \|f\|_(L^2(B_r(a_j)))^2.
            $
            Hence
            $
            \|f\|_(L^2(V))^2 <= sum_(j = 1)^k \|f\|_(L^2(B_(r/2)(a_j)))^2 <= (1)/(2^(2n+2)) sum_(j = 1)^k \|f\|_(L^2(B_r(a_j)))^2 <= (k)/(2^(2n+2)) \|f\|_(L^2(U))^2 <= epsilon^2 \|f\|_(L^2(U))^2,
            $
            which completes the proof.
        
     $qed$
]

#lemma[
    For $cal W subset.double cal B subset.double cal(U) subset.double cal(U)'$ with open sets isomorphic to disks, there exists $c > 0$ such that for all $xi in Z_(L^2)^1(cal B, cal(O))$, exists $zeta in Z_(L^2)^1(cal(U), cal(O))$, $eta in C_(L^2)^0(cal(U), cal(O))$ such that
    $
    zeta = xi + delta eta " on " cal W, 
    $
    and
    $
    limits("max") (\|zeta\|_(L^2(cal W)), \|eta\|_(L^2(cal W))) <= c \|xi\|_(L^2(cal B)).
    $
    
]

#proof[
        Since $H^1(cal B, cal(E)) = 0$, there exists $(g_i) in C^0(cal B, cal(E))$ such that $f_(i j) = g_j - g_i$ on every $V_i inter V_j$, then
        $
        d'' g_j - d'' g_i = d'' f_(i j) = 0 ~> d'' g_i = d'' g_j " on " V_i inter V_j,
        $
        hence there exists $omega in cal(E)^(0, 1)(|cal B|)$ such that $omega|_(V_i) = d'' g_i$ for every $i$. 

        Since $|cal W| subset.double |cal B|$, by partition of unity, exists $psi in C^oo(|cal B|)$ such that $psi|_(|cal W|) = 1$ and $"supp" (psi) subset |cal B|$, then $psi omega in cal(E)^(0, 1)(|cal(U)'|)$. By Dolbeault's lemma, $exists h_i in cal(E)(U_i')$ such that $d'' h_i = psi omega$ on each $U_i'$. Since $d''(h_i - h_j) = 0$ on $U_i' inter U_j'$, let $F_(i j) in cal(O)(U_i' inter U_j')$ such that $F_(i j) = h_j - h_i$ on $U_i' inter U_j'$, so $F_(k l) = F_(k i) + F_(i l)$, impling that $F|_(cal(U)) in Z_(L^2)^1(cal(U), cal(O))$. On $W_i$, $d''h_i = psi omega = omega = d'' g_i$, hence $d''(h_i - g_i) = 0$ on $W_i$, so there exists $eta in C_(L^2)^0(cal W, cal(O))$ such that $eta|_(W_i) = h_i - g_i$ for every $i$. Now, 
        $
        F_(i j) - f_(i j) = (h_j - h_i) - (g_j - g_i) = (h_j - g_j) - (h_i - g_i) = eta_j - eta_i " on " W_i inter W_j,
        $
        hence $zeta := F|_(cal(U))$ and $eta$ satisfy the required conditions. 

        For the estimate, let
        $
        H := Z_(L^2)^1(cal(U), cal(O)) times Z_(L^2)^1(cal B, cal(O)) times C_(L^2)^0(cal W, cal(O))
        $
        with the norm
        $
        \|(zeta, xi, eta)\|_H := (\|zeta\|_(L^2(cal(U)))^2 + \|xi\|_(L^2(cal B))^2 + \|eta\|_(L^2(cal W))^2)^(1/2). 
        $
        Let $L subset H$ be the subspace
        $
        L := \{ (zeta, xi, eta) in H: zeta = xi + delta eta " on " cal W \}.
        $
        Then $L$ is a closed subspace of $H$, hence also a Hilbert space. Consider the projection map $pi: L -> Z_(L^2)^1(cal B, cal(O))$ defined by $pi(zeta, xi, eta) = xi$. By the first part, $pi$ is surjective, hence by the open mapping theorem, there exists $c > 0$ such that for all $xi in Z_(L^2)^1(cal B, cal(O))$, there exists $(zeta, xi, eta) in L$ such that $\|(zeta, xi, eta)\|_H <= c \|xi\|_(L^2(cal B))$. In particular, $limits("max") (\|zeta\|_(L^2(cal W)), \|eta\|_(L^2(cal W))) <= c \|xi\|_(L^2(cal B))$, which completes the proof.
     $qed$
]

#proposition[
    $exists$ a finite-dimensional subspace $S subset Z^1(cal(U), cal(O))$ such that for all $xi in Z^1(cal(U), cal(O))$, there exists $sigma in S$, $eta in C^0(cal W, cal(O))$ such that $sigma = xi + delta eta$ on $cal W$.
    
]

#proof[
        Let $c$ be given in the previous lemma and $epsilon = 1/2c$. By the previous proposition, there exists a finite codimensional subspace $A subset Z_(L^2)^1(cal(U), cal(O))$ such that for all $xi in A$, 
        $
        \|xi\|_(L^2(cal B)) < epsilon \|xi\|_(L^2(cal(U))).
        $
        Pick $S$ to be the orthogonal complement of $A$ in $Z_(L^2)^1(cal(U), cal(O))$, then $S$ is finite-dimensional. For $xi in Z^1(cal(U), cal(O))$, let $M = \|xi\|_(L^2(cal B)) < oo$. Then by the previous lemma, there exists $zeta_0 in Z_(L^2)^1(cal(U), cal(O))$, $eta_0 in C_(L^2)^0(cal W, cal(O))$ such that $zeta_0 = xi + delta eta_0$ on $cal W$ and $limits("max") (\|zeta_0\|_(L^2(cal W)), \|eta_0\|_(L^2(cal W))) <= c M$. Write $zeta_0 = xi_0 + sigma_0$ for some $xi_0 in A$ and $sigma_0 in S$, then
        $
        \|xi_0\|_(L^2(cal B)) <= epsilon \|xi_0\|_(L^2(cal(U))) <= epsilon c M = (M)/(2). 
        $
        By key lemma again, there exists $zeta_1 in Z_(L^2)^1(cal(U), cal(O))$, $eta_1 in C_(L^2)^0(cal W, cal(O))$ such that $zeta_1 = xi_0 + delta eta_1$ on $cal W$ and $limits("max") (\|zeta_1\|_(L^2(cal W)), \|eta_1\|_(L^2(cal W))) <= c M/2$. Write $zeta_1 = xi_1 + sigma_1$ for some $xi_1 in A$ and $sigma_1 in S$, then
        $
        \|xi_1\|_(L^2(cal B)) <= epsilon \|xi_1\|_(L^2(cal(U))) <= epsilon c M/2 = (M)/(4).
        $
        Continue this process, we have $xi_n in A$ such that $\|xi_n\|_(L^2(cal B)) <= M/2^n$ for every $n$, and
        $
        sum_(i=0)^k xi_i + sum_(i=0)^k sigma_i = sum_(i=0)^k zeta_i = sum_(i=0)^k xi + delta sum_(i=0)^k eta_i " on " cal W, 
        $
        impling that
        $
        xi_k + sum_(i=0)^k sigma_i = xi + delta sum_(i=0)^k eta_i " on " cal W
        $
        for every $k$. Define the series
        $
        sigma := sum_(i=0)^oo sigma_i, quad  eta := sum_(i=0)^oo eta_i,
        $
        then $sigma$ converges since $S$ is finite-dimensional and $\|sigma_i\|_(L^2(cal(U))) <= \|zeta_i\|_(L^2(cal(U))) <= c M/2^i$ for every $i$, and $eta$ converges since $\|eta_i\|_(L^2(cal(U))) <= c M/2^i$ for every $i$. Moreover, $sigma = xi + delta eta$ on $cal W$, which completes the proof.
     $qed$
]

We say that a sequence of sheaf homomorphisms
$
cal(F) xarrow(alpha) cal G xarrow(beta) cal H
$
is exact at $cal G$ if for each $x in X$, the sequence of stalks
$
cal(F)_x xarrow(alpha_x) cal G_x xarrow(beta_x) cal H_x
$
is exact at $cal G_x$, i.e. $"ker" beta_x = "Im" alpha_x$. 

#theorem[
    Suppose $X$ is a topological space and
    $
    0 -> cal(F) xarrow(alpha) cal G xarrow(beta) cal H -> 0
    $
    is an exact sequence of sheaves on $X$. Then the induced sequence of cohomology groups
    $
    0 -> H^0(X, cal(F)) xarrow(alpha_*) H^0(X, cal G) xarrow(beta_*) H^0(X, cal H) \
    xarrow(delta) H^1(X, cal(F)) xarrow(alpha_*) H^1(X, cal G) xarrow(beta_*) H^1(X, cal H)
    $
    is exact. 
]

#example[
    By Dolbeault's lemma, we have an exact sequence of sheaves
    $
    0 -> cal(O) -> cal(E) xarrow(d'') cal(E)^(0, 1) -> 0,
    $
    hence we have an exact sequence of cohomology groups
    $
    0 -> H^0(X, cal(O)) -> H^0(X, cal(E)) xarrow(d'') H^0(X, cal(E)^(0, 1)) \
    xarrow(delta) H^1(X, cal(O)) -> H^1(X, cal(E)) xarrow(d'') H^1(X, cal(E)^(0, 1)).
    $
    Since $H^1(X, cal(E)) = 0$ by the partition of unity, we have an isomorphism
    $
    H^1(X, cal(O)) tilde.equiv cal(E)^(0, 1)(X)/d'' cal(E)(X).
    $
]

== Riemann-Roch Theorem

#definition[
    
    
        + 	 Let $X$ be a Riemann surface. A divisor on $X$ is a mapping $D: X -> ZZ$ such that for all $K subset X$ with $K$ compact, we have $D(x) = 0$ for all but finitely many $x in K$.
        + 	 $(D_1 + D_2)(x) = D_1(x) + D_2(x)$ for every $x in X$, hence the set of divisors $"Div" (X)$ on $X$ forms an abelian group. 
        + 	 For $D_1, D_2 in "Div" (X)$, we say $D_1 >= D_2$ if $D_1(x) >= D_2(x)$ for every $x in X$. 
        + 	 For $f in cal(M)(X)$, $a in X$, define the order of $f$ at $a$ by
        $
        "ord"_a(f) = cases(
            0 & "if" f "is holomorphic at" a "and" f(a) != 0,
            k & "if" f "has a zero of order" k "at" a,
            -k & "if" f "has a pole of order" k "at" a,
            oo & "if" f "is identically zero on a neighborhood of" a,
        )
        $
        The principal divisor associated to $f$ is defined by
        $
        (f)(x) = "ord"_x(f) " for every " x in X.
        $
        + 	 $D_1 tilde.op D_2$ are linearly equivalent if $D_1 - D_2$ is a principal divisor, i.e. there exists $f in cal(M)(X)$ such that $D_1 - D_2 = (f)$, then $tilde.op$ is an equivalence relation on $"Div" (X)$, and the set of equivalence classes $"Pic" (X) := "Div" (X)/tilde.op$ is called the Picard group of $X$.
        + 	 On compact Riemann surfaces, define the degree of a divisor $D$ by $"deg" D = sum_(x in X) D(x)$, then $"deg" (f) = 0$ for every $f in cal(M)(X)$, hence $"deg"$ induces a group homomorphism $"deg": "Pic" (X) -> ZZ$. 
        + 	 For $D in "Div" (X)$, $U subset X$ open, define
        $
        cal(O)_D(U) = \{ f in cal(M)(U): (f) + D >= 0 " on " U \}.
        $
        Then $cal(O)_D$ is a sheaf on $X$. In particular, when $D = 0$, $cal(O)_D = cal(O)$. 
        + 	 For linearly equivalent divisors $D_1 tilde.op D_2$, say $D_1 = D_2 + (g)$ for some $g in cal(M)(X)$, then we have an isomorphism of sheaves
        $
        cal(O)_(D_1) -> cal(O)_(D_2), quad  f |-> f g,
        $
        + 	 On compact Riemann surfaces, if $D$ is a divisor with $"deg" D < 0$, then $H^0(X, cal(O)_D) = cal(O)_D(X) = 0$ since on compact Riemann surfaces, a meromorphic function has as many zeros as poles counting multiplicity, hence if such $(f) + D >= 0$ for some $f in cal(M)(X)$, then $f$ must be identically zero. 
    
]

#definition[
    The skyscraper sheaf $CC_p$ at $p in X$ is defined by
    $
    CC_p(U) = cases(
        CC & "if" p in U,
        0 & "if" p in.not U,
    )
    $
]

#proposition[
    $H^0(X, CC_p) = CC$ and $H^1(X, CC_p) = 0$ for every $p in X$.
    
]

#proof[
        Clearly $H^0(X, CC_p) = CC_p(X) = CC$. Given an open cover $cal(U) = (U_i)_(i in I)$ and $(f_(i j)) in Z^1(cal(U), CC_p)$, we can find a refinement $cal V = (V_i)_(i in I)$ of $cal(U)$ such that $p in V_1$ and $p in.not V_i$ for every $i != 1$, then $p in.not V_i inter V_j$ for every $i != j$, hence $f_(i j) = 0$ for every $i, j$, so $xi = (f_(i j))$ is a coboundary, i.e. $xi in B^1(cal V, CC_p)$, hence $H^1(X, CC_p) = 0$.
     $qed$
]

Define a sheaf homomorphism $beta: cal(O)_(D+p) -> CC_p$ as follows. Let $U subset X$ be an open set. If $p in.not U$, then $beta_U = 0$ is the zero map. If $p in U$ and $f in cal(O)_(D+p)(U)$, then $f$ has a Laurent expansion at $p$ of the form
$
f(z) = sum_(n = -k-1)^oo c_n (z-p)^n
$
where $k = D(p)$. Define $beta_U(f) = c_(-k-1)$. Clearly $beta_U$ is a sheaf homomorphism, and we have an exact sequence of sheaves
$
0 -> cal(O)_D -> cal(O)_(D+p) xarrow(beta) CC_p -> 0.
$
This exact sequence induces a long exact sequence of cohomology groups
$
0 -> H^0(X, cal(O)_D) -> H^0(X, cal(O)_(D+p)) xarrow(beta_*) CC \
xarrow(delta) H^1(X, cal(O)_D) -> H^1(X, cal(O)_(D+p)) -> 0
$

#theorem(name: "Riemann-Roch theorem")[ 
    Let $X$ be a compact Riemann surface and $D$ be a divisor on $X$. Then
    $
    dim H^0(X, cal(O)_D) - dim H^1(X, cal(O)_D) = "deg" D - g + 1. 
    $
    
]

#proof[
        The long exact sequence of cohomology groups can be split into three short exact sequences
        $
            0 -> H^0(X, cal(O)_D) -> H^0(X, cal(O)_(D+p)) xarrow(beta_*) "Im" beta_* -> 0, \
            0 -> "Im" beta_* xarrow(delta) CC -> "Im" delta -> 0, \
            0 -> "Im" delta -> H^1(X, cal(O)_D) -> H^1(X, cal(O)_(D+p)) -> 0.
        $
        Therefore, 
        $
            dim H^0(X, cal(O)_(D+p)) = dim H^0(X, cal(O)_D) + dim "Im" beta_*, \
            1 = dim "Im" beta_* + dim "Im" delta, \
            dim H^1(X, cal(O)_D) = dim "Im" delta + dim H^1(X, cal(O)_(D+p)).
        $
        Summing up the first and third equations and subtracting the second equation, we have
        $
            dim H^0(X, cal(O)_(D+p)) + dim H^1(X, cal(O)_(D+p)) = dim H^0(X, cal(O)_D) + dim H^1(X, cal(O)_D) + 1 \
            => dim H^0(X, cal(O)_(D+p)) - dim H^1(X, cal(O)_(D+p)) = dim H^0(X, cal(O)_D) - dim H^1(X, cal(O)_D) + 1.
        $
        Hence if the result holds for $D$, then it also holds for $D + p$, and conversely if the result holds for $D + p$, then it also holds for $D$. We can verify that the result holds for $D = 0$ since $H^0(X, cal(O)) = CC$ and $dim H^1(X, cal(O)) = g$ by definition, hence the result holds for every divisor $D$ by induction on $"deg" D$.
     $qed$
]

#lemma[
    Let $X$ be a compact Riemann surface of genus $g$ and $a in X$. Then there exists a non-constant meromorphic function on $X$ with only pole at $a$ of order at most $g + 1$.
    
]

#proof[
        Let $D = (g + 1) a$. By Riemann-Roch theorem, we have
        $
        dim H^0(X, cal(O)_D) >= (g + 1) - g + 1 = 2,
        $
        hence there exists a non-constant meromorphic function $f in cal(O)_D(X)$, which has only pole at $a$ of order at most $g + 1$.
     $qed$
]

#lemma[
    Suppose $X$ is a compact Riemann surface of genus $g$. Then there exists a holomorphic covering map $X -> PP^1$ with at most $g + 1$ sheets.
    
]

#proof[
        Let $a in X$ and $f$ be a non-constant meromorphic function on $X$ with only pole at $a$ of order at most $g + 1$ given by the previous corollary, then $f: X -> PP^1$ is a holomorphic covering map with at most $g + 1$ sheets.
     $qed$
]

#lemma[
    Every compact Riemann surface of genus $0$ is isomorphic to $PP^1$.
    
]

#proof[
        By the previous corollary, there exists a holomorphic covering map $f: X -> PP^1$ with at most $1$ sheet, hence $f$ is an isomorphism.
     $qed$
]

== Serre Duality

Recall that $omega$ is the sheaf of holomorphic $1$-forms on $X$, $cal(E)^(1, 0)$ is the sheaf of smooth $1$-forms of type $(1, 0)$ on $X$, and $cal(E)^((2))$ is the sheaf of smooth $2$-forms on $X$. For each $omega in cal(E)^((2))(U)$, we can write $omega = f d x and d y$ for some $f in cal(E)(U)$ locally. By Dolbeault's lemma, there exists $g in cal(E)(U)$ such that
$
(partial)/(partial overline(z)) g = -f ~> d(g d z) = f d z and d overline(z) = omega,
$
hence we have an exact sequence of sheaves
$
0 -> omega -> cal(E)^(1, 0) xarrow(d) cal(E)^((2)) -> 0, 
$
inducing a long exact sequence of cohomology groups
$
0 -> H^0(X, omega) -> H^0(X, cal(E)^(1, 0)) xarrow(d) H^0(X, cal(E)^((2))) \
xarrow(delta) H^1(X, omega) -> H^1(X, cal(E)^(1, 0)) xarrow(d) H^1(X, cal(E)^((2))).
$
Similar to how $H^1(X, cal(E)) = 0$, we also have $H^1(X, cal(E)^(1, 0)) = 0$ and $H^1(X, cal(E)^((2))) = 0$ by the partition of unity, hence we have an isomorphism
$
H^1(X, omega) tilde.equiv cal(E)^((2))(X)/d cal(E)^(1, 0)(X).
$

Let $omega in cal(M)^((1))(X)$ be a meromorphic $1$-form on $X$. For $x in X$ and a neighborhood $U$ of $x$, write $omega|_U = f d z$ for some $f in cal(M)(U)$, then define the order of $omega$ at $x$ by
$
"ord"_x(omega) = "ord"_x(f).
$
This is well-defined since if $omega|_U = g d w$ for some $g in cal(M)(U)$ and local coordinate $w$, then $f d z = g d w$, hence $f = g (d w)/(d z)$, so $"ord"_x(f) = "ord"_x(g) + "ord"_x((d w)/(d z)) = "ord"_x(g)$ since $(d w)/(d z)$ is holomorphic and non-vanishing at $x$. For $omega in cal(M)^((1))(X)^*$, the principal divisor associated to $omega$ is defined by
$
(omega)(x) = "ord"_x(omega) " for every " x in X, 
$
called the canonical divisor associated to $omega$. For any $omega_1, omega_2 in cal(M)^((1))(X)^*$, locally write
$
omega_1|_U = f_1 d z, quad  omega_2|_U = f_2 d z,
$
and set $f|_U = (f_1)/(f_2) in cal(M)(U)^*$ and thus $omega_1 = f omega_2$ on $U$. By sheaf axiom, we can glue $f|_U$ to a global meromorphic function $f$ on $X$, hence $omega_1 = f omega_2$ on $X$, so $(omega_1) - (omega_2) = (f)$ is a principal divisor, hence the canonical divisor is unique up to linear equivalence, denoted by $K$.

Define
$
omega_(-D)(U) = \{ omega in cal(M)^((1) \}(U)^*: (omega) - D >= 0 " on " U)
$
for every divisor $D$ on $X$, then $omega_(-D)$ is a sheaf on $X$. In particular, when $D = 0$, $omega_0 = omega$. 

#proposition[
    There is a natural isomorphism
    $
    cal(O)_(K-D) xarrow(tilde.op) omega_(-D), quad  f |-> f omega,
    $
    where $K$ is the canonical divisor associated to $omega$.
    
]

#proof[
        Follows from
        $
        (f) + (K) - D >= 0 iff (f omega) + (-D) >= 0
        $
        for every $f in cal(M)(X)^*$ and $omega in cal(M)^((1))(X)^*$.
     $qed$
]

#proposition[
    The degree of the canonical divisor $K$ is $2g - 2$, where $g$ is the genus of $X$.
    
]

#proof[
        By Riemann-Roch theorem, we have
        $
        1 - g + "deg" K &= dim H^0(X, cal(O)_K) - dim H^1(X, cal(O)_K) \
        &= dim H^0(X, omega) - dim H^1(X, omega) \
        &= dim H^1(X, cal(O))^* - dim H^0(X, cal(O))^* = g - 1,
        $
        hence $"deg" K = 2g - 2$.
     $qed$
]

#theorem(name: "Serre duality")[ 
    Let $X$ be a compact Riemann surface. Then there is a natural isomorphism
    $
    H^0(X, omega_(-D)) tilde.equiv H^1(X, cal(O)_D)^*
    $
    for every divisor $D$ on $X$. 
    #proof[
        Our goal is to construct a natural bilinear pairing
        $
        H^0(X, omega_(-D)) times H^1(X, cal(O)_D) -> CC
        $
        such that the induced map $H^0(X, omega_(-D)) -> H^1(X, cal(O)_D)^*$ is an isomorphism. For $omega in H^0(X, omega_(-D))$ and $xi = (f_(i j)) in Z^1(cal(U), cal(O)_D)$ for some open cover $cal(U) = (U_i)_(i in I)$, their product $omega dot xi$ is $(f_(i j) omega) in Z^1(cal(U), omega)$. Recall that
        $
        H^1(X, omega) tilde.equiv cal(E)^((2))(X)/d cal(E)^(1, 0)(X),
        $
        so we define the residue map from $H^1(X, omega)$ to $CC$ as follows. For $eta in H^1(X, omega)$, let $tau$ be a representative of $eta$ in $cal(E)^((2))(X)$, then define
        $
        "Re"s (eta) = integral.double_X tau.
        $
        In practice, to compute the RHS, we need to find a finite covering of $X$, then find a partition of unity subordinate to the covering, and compute the integral of $tau$ on each open set in the covering, then sum up the integrals. To verify that the residue map is well-defined, let $tau' = tau + d f$ for some $f in cal(E)^(1, 0)(X)$, then by Stokes' theorem,
        $
        integral.double_X tau' = integral.double_X tau + integral.double_X d f = integral.double_X tau + integral_(partial X) f = integral.double_X tau,
        $
        hence the residue map is well-defined. Now we define the bilinear pairing by
        $
        chevron.l omega, xi chevron.r = "Re"s (omega dot xi) " for every " omega in H^0(X, omega_(-D)) " and " xi in H^1(X, cal(O)_D).
        $
        The induced map $iota_D$ is $omega |-> chevron.l omega, dot chevron.r$, which is a linear map from $H^0(X, omega_(-D))$ to $H^1(X, cal(O)_D)^*$. To verify that $iota_D$ is injective, we need to show that for all nonzero meromorphic 1-form $omega in H^0(X, omega_(-D))$, there exists $xi in H^1(X, cal(O)_D)$ such that $chevron.l omega, xi chevron.r != 0$. Since $D$ is finite, we can find $a in X$ such that $D(a) = 0$. Let $U_0$ be a neighborhood of $a$ such that $U_0 tilde.equiv B_R (0) subset CC$ and $a$ corresponds to $0$. By shrinking $U_0$ if necessary, we can assume that $omega|_(U_0) = f d z$ with $f$ holomorphic and non-vanishing on $U_0$, except possibly a zero at $a$. Let $U_1 = X without \{a\}$, then $cal(U) = (U_0, U_1)$ is an open cover of $X$. Let $f_0 = 1/(z f) in cal(O)_D(U_0)$ and $f_1 = 0 in cal(O)_D(U_1)$, then $mu = (f_0, f_1) in C^0(cal(U), cal(O)_D)$ and $delta mu = (f_(i j)) in Z^1(cal(U), cal(O)_D)$ with $f_(01) = -f_(10) = 1/(z f)$ on $U_0 inter U_1$. Let $xi = overline(delta mu) in H^1(X, cal(O)_D)$, then
        $
        chevron.l omega, xi chevron.r = "Re"s (omega dot xi) = "Re"s (delta (omega mu)). 
        $
        Let $zeta = omega mu = (omega_0, omega_1) = (d z/z, 0)$. We need to find a representative of $delta zeta$ in $cal(E)^((2))(X)$ to compute the residue. Since $delta zeta in Z^1(cal(U), omega) subset Z^1(cal(U), cal(E)^(1, 0)) = B^1(cal(U), cal(E)^(1, 0))$, there exists $(sigma_0, sigma_1) in C^0(cal(U), cal(E)^(1, 0))$ such that $omega_0 - omega_1 = sigma_0 - sigma_1$ on $U_0 inter U_1$. Since $omega_0 - omega_1 = d z/z$ is holomorphic on $U_0 inter U_1$, we have
        $
        d(omega_0 - omega_1) = d''(omega_0 - omega_1) = 0  ~> d sigma_0 = d sigma_1 " on " U_0 inter U_1,
        $
        hence we can glue $d sigma_0$ and $d sigma_1$ to a global smooth 2-form $tau$ on $X$, which is a representative of $delta zeta$ in $cal(E)^((2))(X)$. Pick a smaller $V_0 subset U_0$ such that $V_0 tilde.equiv B_epsilon (0)$ for some $epsilon < R$, then by partition of unity exists $psi in cal(E)(X)$ such that $psi|_(V_0) = 1$ and $psi|_(X without U_0) = 0$. Then
        $
        integral.double_X d(psi sigma_1) &= integral.double_(U_0) d(psi sigma_1) = integral.double_(U_0) d psi sigma_0 - integral.double_(U_0) d psi omega_0 - integral.double_(U_0) psi d omega_1 \
        &= integral.double_(U_0) d psi omega_0 = -lim_(epsilon' -> 0) integral.double_(epsilon' <= |z| <= R) d psi omega_0 \
        &= -integral.double_(epsilon <= |z| <= R) d psi omega_0 = integral_(|z| = epsilon) psi omega_0 = 2pi i. 
        $
        Set $phi.alt = 1 - psi$, then $phi.alt|_(V_0) = 0$ and $phi.alt|_(X without U_0) = 1$, hence
        $
        integral.double_X tau &= integral.double_X d(psi sigma_1) + integral.double_X d(phi.alt sigma_0) \
        &= integral.double_X d(psi sigma_1) + integral.double_(U_0) d phi.alt sigma_0 = 2pi i. 
        $
        Hence $chevron.l omega, xi chevron.r = 2pi i/2pi i = 1 != 0$, which implies that $iota_D$ is injective. 

        #lemma[
            Let $D, B in "Div" (X)$, then $psi in H^0(X, omega_B)$ induces an isomorphism $H^1(X, cal(O)_(D-B)) -> H^1(X, cal(O)_D)$. Taking dual, we have mapping
            $
            H^1(X, cal(O)_D)^* xarrow(psi^*) H^1(X, cal(O)_(D-B))^*. 
            $
            If $psi != 0$, then $psi^*$ is injective. 
            
]

#proof[
                Let $A := (psi)$ be the principal divisor associated to $psi$. If $A + B >= 0$, we have
                $
                cal(O)_(D-B) arrow.r.hook cal(O)_(D+A) tilde.equiv cal(O)_D
                $
                since $A+B >= 0$. 

                If $D+A = (D-B) + p_1 + dots + p_m$, then
                $
                0 -> cal(O)_((D-B)+p_1 + dots + p_(m-1)) -> cal(O)_(D+A) -> CC_(p_m) -> 0
                $
                is an exact sequence of sheaves, inducing a long exact sequence of cohomology groups
                $
                0 -> H^0(X, cal(O)_((D-B)+p_1 + dots + p_(m-1))) -> H^0(X, cal(O)_(D+A)) -> CC \
                xarrow(delta) H^1(X, cal(O)_((D-B)+p_1 + dots + p_(m-1))) -> H^1(X, cal(O)_(D+A)) -> 0.
                $
                In particular, we have a surjection $H^1(X, cal(O)_(D-B)) -> H^1(X, cal(O)_(D+A)) tilde.equiv H^1(X, cal(O)_D)$, hence $psi^*$ is injective. 
             $qed$
]

        Suppose $Lambda in H^1(X, cal(O)_D)^*$ is a nonzero linear functional, we need to show that there exists $omega in H^0(X, omega_(-D))$ such that $iota_D(omega) = Lambda$. 

        For $p in X$, let $D_n = D - n p$, then $psi in H^0(X, cal(O)_(n p))$ induces an injective map
        $
        H^1(X, cal(O)_D)^* xarrow(psi^*) H^1(X, cal(O)_(D_n))^*.
        $
        Let
        $
        Lambda = \{ psi Lambda | psi in H^0(X, cal(O)_(n p \})) subset H^1(X, cal(O)_(D_n))^*,
        $
        then $Lambda$ is a linear subspace of $H^1(X, cal(O)_(D_n))^*$. By Riemann-Roch theorem, we have $dim Lambda = dim H^0(X, cal(O)_(n p)) >= n - g + 1$, hence $dim Lambda -> oo$ as $n -> oo$. On the other hand, by Riemann-Roch theorem again, we have
        $
        dim "Im" (iota_(D_n)) = dim H^0(X, omega_(-D_n)) = dim H^1(X, cal(O)_(K-D_n)) + 1 - g + "deg" (K - D_n). 
        $
        For $n > "deg" D$, we have $H^0(X, cal(O)_(D_n)) = 0$, hence $dim H^1(X, cal(O)_(D_n))^* = g - 1 + "deg" D_n = g - 1 + "deg" D - n$. We can pick $n$ large enough such that
        $
        dim Lambda + dim "Im" (iota_(D_n)) > dim H^1(X, cal(O)_(D_n))^*,
        $
        hence $Lambda inter "Im" (iota_(D_n)) != 0$, so there exists $psi Lambda in iota_(D_n)(omega_n)$ with $omega_n in H^0(X, omega_(-D_n))$. Since $psi in H^0(X, cal(O)_(n p))$, we have $A + n p >= 0$ and $1/psi in H^0(X, cal(O)_A)$. Let $D' = D_n - A = D - n p - A$, then $D' <= D$ so $0 -> cal(O)_(D') arrow.r.hook cal(O)_D$ is an injection of sheaves, inducing a surjection
        $
        pi: H^1(X, cal(O)_(D')) -> H^1(X, cal(O)_D).
        $
        Define $iota_(D')^D(Lambda) := Lambda compose pi in H^1(X, cal(O)_(D'))^*$. Since $psi Lambda = iota_(D_n)(omega_n)$, functoriality of the pairing gives
        $
        iota_(D')^D(Lambda) = iota_(D')\!((1)/(psi)omega_n).
        $

        We claim that $omega_0 := (1)/(psi) omega_n in H^0(X, omega_(-D))$. If not, then there exists $a in X$ such that $"ord"_a(omega_0) < D(a)$. Let $U_0$ be a neighborhood around $a$ isomorphic to a disk in $CC$ such that $a$ corresponds to $0$, and $omega_0|_(U_0) = f d z$ for some $f$ with no zeros or poles in $U_0 without \{ a \}$, and $D|_(U_0 without \{ a \}) = 0$ and $D'|_(U_0 without \{ a \}) = 0$. Set $U_1 = X without \{ a \}$, then $cal(U) = (U_0, U_1)$ is an open cover of $X$. Let $f_0 = 1/(z f) in cal(O)_M(U_0)$ and $f_1 = 0 in cal(O)_M(U_1)$, then $eta = (f_0, f_1) in C^0(cal(U), cal(M))$, then
        $
        & omega_0 eta = (omega_0 f_0, omega_0 f_1) = (d z/z, 0) in C^0(cal(U), cal(M)^((1))) \
        => & "ord"_a(omega_0 eta) = -1 \
        => & "ord"_a(eta) = -1 - "ord"_a(omega_0) >= -D(a) \
        => & eta in C^0(cal(U), cal(O)_(D)) \
        => & delta eta in Z^1(cal(U), cal(O)_D) \
        => & xi = [delta eta] = 0 in H^1(X, cal(O)_D). 
        $
        Note that $delta eta in Z^1(cal(U), cal(O)_D) = Z^1(cal(U), cal(O)_(D'))$. Let $zeta' := [delta eta] in H^1(X, cal(O)_(D'))$. Therefore, 
        $
        chevron.l omega_0, zeta' chevron.r = iota_(D')^D (Lambda)(xi) = Lambda(xi) = 0 ~> chevron.l omega_0, zeta' chevron.r = "Re"s (omega_0 dot eta) = 1.
        $
        This is a contradiction, hence $omega_0 in H^0(X, omega_(-D))$. 
     $qed$
]
]

== Mittag-Leffler Problem

Let $X$ be a compact Riemann surface of genus $g >= 1$. Recall that for $p in X$, by Riemann-Roch, there exists a holomorphic covering map $f: X -> PP^1$ with at most $g + 1$ sheets. We would like to know whether we can find a holomorphic covering map $f: X -> PP^1$ with at most $g$ sheets. If such mapping exists, then on a local coordinate $z$ around $p$ with $z(p) = 0$, the principal part of $f$ at $p$ is of the form
$
sum_(i=0)^(g-1) (c_i)/(z^(i+1))
$
with $(c_0, dots.h, c_(g-1)) != 0$. 

#definition[
    Let $mu = (f_i) in C^0(frak(U), cal(M))$ for some open cover $frak(U) = (U_i)_(i in I)$ of $X$. We say $mu$ is a Mittag-Leffler distribution if $delta mu in Z^1(frak(U), cal(O))$, i.e. $f_i - f_j$ is holomorphic on $U_i inter U_j$ for every $i, j$. We say $f in cal(M)(X)$ is a solution to $mu$ if $f - f_i in cal(O)(U_i)$ for every $i$.
]

#proposition[
    $mu in C^0(frak(U), cal(M))$ has a solution if and only if $delta mu = 0$ in $H^1(X, cal(O))$.
    
]

#proof[
        + "$=>$": If $f$ is a solution to $mu$, then set $g_i = f_i - f in cal(O)(U_i)$, then $f_j - f_i = g_j - g_i$ on $U_i inter U_j$, hence $delta mu = 0$ in $H^1(X, cal(O))$.
        + "$<=$": If $delta mu = 0$ in $H^1(X, cal(O))$, then there exists $g = (g_i) in C^0(frak(U), cal(O))$ such that $f_j - f_i = g_j - g_i$ on $U_i inter U_j$, hence we can glue $f_i - g_i$ to a global meromorphic function $f$ on $X$, which is a solution to $mu$.
    $qed$
]

#theorem[
    $mu$ has a solution if and only if $"Re"s (omega mu) = 0$ for every $omega in H^0(X, omega)$.
    
]

#proof[
        $
        mu "has a solution" iff & delta mu = 0 " in " H^1(X, cal(O)) \
        iff & Lambda(delta mu) = 0 " for every " Lambda in H^1(X, cal(O))^* \
        iff & chevron.l omega, delta mu chevron.r = 0 " for every " omega in H^0(X, omega) \
        iff & "Re"s (omega mu) = 0 " for every " omega in H^0(X, omega).
        $
     $qed$
]

Let $omega_1, dots.h, omega_g$ be a basis of $omega(X)$. On a coordinate neighborhood $U$ around $p$ with coordinate $z$ such that $z(p) = 0$, we can write
$
omega_k = f_k d z = sum_(i=0)^oo a_(k i) z^i d z " for every " k = 1, dots.h, g.
$
Consider the covering $frak(U) = (U, X without \{p\})$ and the Mittag-Leffler distribution $mu = (h, 0) in C^0(frak(U), cal(M))$ with $h = sum_(i=0)^(g-1) (c_i)/(z^(i+1))$ for some $(c_0, dots.h, c_(g-1)) != 0$. By the previous theorem, $mu$ has a solution if and only if
$
"Re"s (omega_k mu) = "Re"s (omega_k h) = sum_(i=0)^(g-1) a_(k i) c_i = 0
$
for every $k = 1, dots.h, g$. Therefore, $mu$ has a solution if and only if the matrix
$
    product_(k=0)^(g-1) (k!) dot mat(
        a_(10), a_(11), dots, a_(1, g-1) ;
        a_(20), a_(21), dots, a_(2, g-1) ;
        dots.v, dots.v, dots.down, dots.v ;
        a_(g 0), a_(g 1), dots, a_(g, g-1)
    ) = 
    mat(
        f_1(0), f_1'(0), dots, f_1^((g-1))(0) ;
        f_2(0), f_2'(0), dots, f_2^((g-1))(0) ;
        dots.v, dots.v, dots.down, dots.v ;
        f_g(0), f_g'(0), dots, f_g^((g-1))(0)
    )
$
is singular, i.e. has zero determinant. Define the above matrix to be the Wronskian matrix of $f_1, dots.h, f_g$ at $p$, and its determinant
$
    W(f_1, dots.h, f_g)(p) = "det" mat(
        f_1(0), f_1'(0), dots, f_1^((g-1))(0) ;
        f_2(0), f_2'(0), dots, f_2^((g-1))(0) ;
        dots.v, dots.v, dots.down, dots.v ;
        f_g(0), f_g'(0), dots, f_g^((g-1))(0)
    )
$
is called the Wronskian of $f_1, dots.h, f_g$ at $p$. For a basis $omega_1, dots.h, omega_g$ of $omega(X)$, the Wronskian $W(omega_1, dots.h, omega_g)(p)$ is defined to be $W(f_1, dots.h, f_g)(p)$, where $omega_k = f_k d z$ on $U$ for every $k$. $p$ is called a Weierstrass point if $W(omega_1, dots.h, omega_g)(p) = 0$ for some (or equivalently, any) basis $omega_1, dots.h, omega_g$ of $omega(X)$, and the weight of $p$ is defined to be the order of zero of $W(omega_1, dots.h, omega_g)$ at $p$.

We need to verify a few things about the Wronskian. 

#proposition[
    If $f_1, dots.h, f_g$ are linearly independent over $CC$, then $W(f_1, dots.h, f_g)$ is not identically zero.
    
]

#proof[
        Proceed by induction on $g$. The case $g = 1$ is trivial. For $g > 1$, assume that $W(f_1, dots.h, f_(g-1))$ is not identically zero, then consider the differential equation in variable $w$:
        $
        "det" mat(
            f_1, f_1', dots, f_1^((g-1)) ;
            f_2, f_2', dots, f_2^((g-1)) ;
            dots.v, dots.v, dots.down, dots.v ;
            f_(g-1), f_(g-1)', dots, f_(g-1)^((g-1)) ;
            w, w', dots, w^((g-1))
        ) = W(f_1, dots.h, f_(g-1)) w^((g-1)) + dots = 0.
        $
        Since $W(f_1, dots.h, f_(g-1))$ is not identically zero, the above equation is a linear differential equation with meromorphic coefficients, hence its solution space has dimension $g-1$. Since $f_1, dots.h, f_(g-1)$ are linearly independent solutions to the above equation, they form a basis of the solution space. Since $f_g$ is not a linear combination of $f_1, dots.h, f_(g-1)$, $f_g$ is not a solution to the above equation, hence $W(f_1, dots.h, f_g)$ is not identically zero.
     $qed$
]

#proposition[
    If $(U, z)$ and $(tilde(U), tilde(z))$ are two charts, then on $U inter tilde(U)$, we have
    $
    W_z(omega_1, dots.h, omega_g) = ((d tilde(z))/(d z))^N W_(tilde(z))(omega_1, dots.h, omega_g),
    $
    where $N = (g(g+1))/(2)$. 
    
]

#proof[
        Write $omega_k = f_k d z = tilde(f)_k d tilde(z)$ on $U inter tilde(U)$, then $f_k = psi tilde(f)_k$ with $psi = (d tilde(z))/(d z) in cal(O)^*(U inter tilde(U))$. Therefore,
        $
        (d^m f_k)/(d z^m) = psi^(m+1) (d^m tilde(f)_k)/(d tilde(z)^m) + "lower order terms in " psi, (d psi)/(d z), dots.h, (d^(m-1)psi)/(d z^(m-1)),
        $
        hence
        $
        W_z(omega_1, dots.h, omega_g) = ((d tilde(z))/(d z))^(1 + 2 + dots + g) W_(tilde(z))(omega_1, dots.h, omega_g).
        $
     $qed$
]

#proposition[
    If $tilde(omega)_1, dots.h, tilde(omega)_g$ is another basis of $omega(X)$, then $W(tilde(omega)_1, dots.h, tilde(omega)_g) = c W(omega_1, dots.h, omega_g)$ for some $c in CC^*$.
    
]

#proof[
        Write $tilde(omega)_k = sum_(j=1)^g c_(j k) omega_j$ for some $C = (c_(j k)) in "GL"_g(CC)$, then on the local coordinate $z$ around $p$ with $z(p) = 0$, we have $tilde(omega)_k = tilde(f)_k d z$ with $tilde(f)_k = sum_(j=1)^g c_(j k) f_j$, hence
        $
        W(tilde(omega)_1, dots.h, tilde(omega)_g) = W(tilde(f)_1, dots.h, tilde(f)_g) = "det" C dot W(f_1, dots.h, f_g) = "det" C dot W(omega_1, dots.h, omega_g). 
        $
     $qed$
]

#theorem[
    $p$ is a Weierstrass point if and only if there exists a non-constant meromorphic function on $X$ with only pole at $p$ of order at most $g$.
    
]

#proof[
        Straightforward from the discussion before the definition of Wronskian.
     $qed$
]

#theorem[
    The weighted sum of Weierstrass points on $X$ is $(g-1)g(g+1)$. 
    
]

#proof[
        Let $(U_i, z_i)_(i in I)$ be a covering of $X$ and $psi_(i j) = (d z_j)/(d z_i) in cal(O)^*(U_i inter U_j)$. Choose a basis $omega_1, dots.h, omega_g$ of $omega(X)$. Let $W_i$ be the Wronskian of $omega_1, dots.h, omega_g$ on $U_i$, then by the previous proposition, we have $W_j = psi_(i j)^N W_i$ on $U_i inter U_j$ with $N = (g(g+1))/(2)$. Define the divisor $D$ by $D(x) = "ord"_x(W_i)$ for $x in U_i$, then $D$ is well-defined since $psi_(i j)$ is non-vanishing, and the weighted sum of Weierstrass points is precisely $"deg" D$. Write $omega_1 = f_(1i) d z_i$ on $U_i$ for every $i$, then $f_(1i) = psi_(i j) f_(1j)$ on $U_i inter U_j$, hence
        $
        f_(1i)^N = psi_(i j)^N f_(1j)^N ~> W_i f_(1i)^(-N) = W_j f_(1j)^(-N) " on " U_i inter U_j.
        $
        Therefore, we can glue $W_i f_(1i)^(-N)$ to a global meromorphic function $f$ on $X$, hence
        $
        D = (f) + N(omega_1) ~> "deg" D = N dot "deg" (omega_1) = N dot (2g - 2) = (g-1)g(g+1).
        $ 
     $qed$
]

#theorem[
    Let $X$ be a compact Riemann surface of genus $g >= 2$, then exists a holomorphic covering $f: X -> PP^1$ with at most $g$ sheets. 
    
]

#proof[
        For surfaces of genus $>= 2$, the previous theorem gurantees the existence of a Weierstrass point, hence there exists a non-constant meromorphic function on $X$ with only pole at $p$ of order at most $g$, i.e. a holomorphic covering $f: X -> PP^1$ with at most $g$ sheets.
     $qed$
]

#lemma[
    Every compact Riemann surface of genus $2$ is hyperelliptic, i.e. there exists a holomorphic covering $f: X -> PP^1$ with at most $2$ sheets.
    
]

#proof[
        By the previous theorem, there exists a holomorphic covering $f: X -> PP^1$ with at most $2$ sheets. If $f$ is a holomorphic covering with only one sheet, then $f$ is an isomorphism, hence $X tilde.equiv PP^1$, which contradicts the assumption that $g = 2$. Therefore, $f$ is a holomorphic covering with exactly two sheets, so $X$ is hyperelliptic.
     $qed$
]

#example[
    Let $Gamma_1, Gamma_2 in CC$ be two linearly independent complex numbers over $RR$, and let $P = \{ t_1 Gamma_1 + t_2 Gamma_2 | 0 <= t_1 < 1, 0 <= t_2 < 1 \}$. Suppose at $a_1, dots.h, a_n in P$, we have prescribed principal parts
    $
    h_j = sum_(k=-r_j)^(-1) c_k^((j)) (z - a_j)^k " for every " j = 1, dots.h, n.
    $
    Then there exists a global meromorphic function $f$ on $cal(M)(CC)$ doubly periodic with respect to $Gamma = ZZ Gamma_1 + ZZ Gamma_2$ with the prescribed principal part $h_j$ at $a_j$ for every $j$ if and only if
    $
    sum_(j=1)^n c_(-1)^((j)) = 0.
    $
    This is straightforward since the existence of such $f$ is equivalent to the existence of a solution to the Mittag-Leffler distribution $mu = (h_1, dots.h, h_n, 0) in C^0(frak(U), cal(M))$ with $frak(U) = (U_1, dots.h, U_n, CC without P)$ and $U_j$ a neighborhood of $a_j$ for every $j$, which is equivalent to $"Re"s (omega mu) = 0$ for every $omega in omega(X)$, where $X = CC\/Gamma$. Since $omega(X)$ is generated by $d z$, we have $"Re"s (omega mu) = "Re"s (d z dot mu) = sum_(j=1)^n c_(-1)^((j))$, hence the existence of such $f$ is equivalent to $sum_(j=1)^n c_(-1)^((j)) = 0$.
]

#proposition[
    If $D$ is a divisor of degree $"deg" D > 2g-2$, then $H^1(X, cal(O)_D) = 0$.
    
]

#proof[
        By Serre duality, we have
        $
        H^1(X, cal(O)_D)^* tilde.equiv H^0(X, omega_(-D)) tilde.equiv H^0(X, cal(O)_(K-D)),
        $
        which equals zero since $"deg" (K-D) < 0$.
     $qed$
]

#proposition[
    Let $X$ be a compact Riemann surface, then $H^1(X, cal(M)) = 0$.
    
]

#proof[
        Fix a 1-cocycle $(f_(i j)) in Z^1(frak(U), cal(M))$. We may assume that $frak(U)$ is finite and the total number of poles of $(f_(i j))$ is finite by passing to a refinement. Thus we can find a divisor $D$ such that $f_(i j) in cal(O)_D(U_i inter U_j)$ for every $i, j$ and $"deg" D > 2g - 2$. By the previous proposition, we have $H^1(X, cal(O)_D) = 0$, hence $(f_(i j)) in B^1(frak(U), cal(O)_D) subset B^1(frak(U), cal(M))$, which implies that $(f_(i j)) = 0$ in $H^1(X, cal(M))$.
     $qed$
]

=== Riemann-Hurwitz Formula

#definition[
    Let $X, Y$ be compact Riemann surfaces, and $f: X -> Y$ be a holomorphic covering map. For $x in X$, the ramification index of $f$ at $x$ is defined to be the positive integer $k$ such that $f$ can be written as $f(z) = z^k$ on a local coordinate $z$ around $x$ with $z(x) = 0$, denoted by $\nu(f, x)$. If $\nu(f, x) > 1$, then $x$ is called a ramification point of $f$, and $f(x)$ is called a branch point of $f$. The branching number $b(f, x)$ is defined to be $\nu(f, x) - 1$. The total branching number of $f$ is defined to be $b = sum_(x in X) b(f, x)$.
]

#theorem[
    Let $X, Y$ be compact Riemann surfaces, and $f: X -> Y$ be a $n$-sheeted holomorphic covering map, then
    $
    g = (b)/(2) + n(g' - 1) + 1,
    $
    where $g$ and $g'$ are the genera of $X$ and $Y$ respectively, and $b$ is the total branching number of $f$.
    
]

#proof[
        Let $omega$ be a non-vanishing meromerphic 1-form on $Y$ and $omega|_V = g(z') d z'$ on a local coordinate $z'$ around $y in Y$ with $z'(y) = 0$. For $x in f^(-1)(y)$, let $z$ be a local coordinate around $x$ with $z(x) = 0$ such that $f(z) = z^k$ with $k = \nu(f, x)$, then
        $
        f^* omega = g(z^k) d(z^k) = k g(z^k) z^(k-1) d z,
        $
        hence
        $
        "ord"_x(f^* omega) = (k - 1) + k dot "ord"_y(omega) = b(f, x) + \nu(f, x) dot "ord"_y(omega).
        $
        Summing over all $x in f^(-1)(y)$ gives
        $
        sum_(x in f^(-1)(y)) "ord"_x(f^* omega) & = sum_(x in f^(-1)(y)) b(f, x) + sum_(x in f^(-1)(y)) \nu(f, x) dot "ord"_y(omega) \
        & = b(f, y) + n dot "ord"_y(omega).
        $
        Summing over all $y in Y$ gives
        $
        "deg"(f^*omega) = sum_(x in X) "ord"_x(f^* omega) = sum_(y in Y) b(f, y) + n dot sum_(y in Y) "ord"_y(omega) = b + n dot "deg" (omega).
        $
        Since $"deg" (omega) = 2g' - 2$ and $"deg" (f^* omega) = 2g - 2$, we have
        $
        2g - 2 = b + n(2g' - 2) ~> g = (b)/(2) + n(g' - 1) + 1).
        $
     $qed$
]

== deRham-Hodge Theorem

Recall that
$
0 -> CC -> cal(E)(X) xarrow(d) cal(E)^((1))(X) xarrow(d) cal(E)^((2))(X) 
$
is a complex of sheaves on $X$, hence we can define the first deRham cohomology group of $X$ to be
$
"Rh" ^1(X) = ("ker" (cal(E)^((1))(X) xarrow(d) cal(E)^((2))(X)))/("Im" (cal(E)(X) xarrow(d) cal(E)^((1))(X))).
$
If $X$ is simply connected, then every closed 1-form on $X$ is exact, hence $"Rh"^1(X) = 0$. If we let $cal L(U) = "ker" (cal(E)^((1))(U) xarrow(d) cal(E)^((2))(U))$ for every open set $U$, then $cal L$ is the sheaf of closed 1-forms on $X$, and we have a short exact sequence of sheaves
$
0 -> CC -> cal(E) xarrow(d) cal L -> 0,
$
which induces a long exact sequence of cohomology groups
$
0 -> H^0(X, CC) -> H^0(X, cal(E)) xarrow(d) H^0(X, cal L) -> H^1(X, CC) -> H^1(X, cal(E)) -> dots.
$
Since $H^1(X, cal(E)) = 0$, we have
$
H^1(X, CC) tilde.equiv (cal L(X))/(d cal(E)(X)) = "Rh"^1(X).
$

#definition[
    
        + 	 For each $omega in cal(E)^((1))(X)$, we can write $omega|_U = f d z + g d overline z$ for some local coordinate $z$ on $U$, then we define $overline omega|_U = overline f d overline z + overline g d z$. 
        + 	 If $omega in omega(X)$ is a holomorphic 1-form on $X$, then $overline omega$ is called an anti-holomorphic 1-form on $X$. We denote the space of anti-holomorphic 1-forms on $X$ by $overline omega(X)$.
        + 	 Define the Hodge star operator $*: cal(E)^((1))(X) -> cal(E)^((1))(X)$ by
        $
        f d z + g d overline z |-> i (overline f d overline z - overline g d z).
        $
        We have $**omega = -omega$, hence $*$ is an isomorphism. Moreover, we can define a positive-definite inner product on $cal(E)^((1))(X)$ by
        $
        chevron.l omega_1, omega_2 chevron.r = integral.double_X omega_1 and *overline omega_2.
        $
        We can verify that
        $
        chevron.l omega, omega chevron.r = integral.double_X omega and *overline omega = 2 integral.double_X (|f|^2 + |g|^2) d x and d y >= 0,
        $
        and $chevron.l omega, omega chevron.r = 0$ if and only if $omega = 0$. Also, 
        $
        overline(chevron.l omega_1\, omega_2 chevron.r) = integral.double_X overline(omega_1) and *omega_2 = integral.double_X *omega_2 and overline(omega_1) = integral.double_X omega_2 and *overline(omega_1) = chevron.l omega_2, omega_1 chevron.r,
        $
        Hence $cal(E)^((1))(X)$ is a unitary space with respect to the above inner product.
    
]

#definition[
    A 1-form $omega in cal(E)^((1))(X)$ is called harmonic if $d omega = 0$ and $d(*omega) = 0$. Locally, if $omega|_U = f d z + g d overline z$, then $omega$ is harmonic if and only if
    $
    (partial g)/(partial z) = ((partial F))/(partial overline z), quad  (partial overline f)/(partial z) = -(partial overline g)/(partial overline z).
    $
    Let $"Harm" ^1(X)$ be the space of harmonic 1-forms on $X$.
]

#proposition[
    Let $omega in cal(E)^((1))(X)$. The following are equivalent:
    
        + $omega$ is harmonic;
        + $d'omega = d''omega = 0$;
        + $omega = omega_1 + omega_2$ for some $omega_1 in omega(X)$ and $omega_2 in overline omega(X)$;
        + For all $a in X$, there exists a neighborhood $U$ around $a$ such that $omega = d f$ for some harmonic function $f$ on $U$.
    
    
]

#proof[
        
        
            + 	 "(i) $=>$ (ii)": Locally, if $omega|_U = f d z + g d overline z$, then
            $
            d'omega = (partial g)/(partial z) d z and d overline z, quad  d''omega = -((partial F))/(partial overline z) d z and d overline z,
            $
            and
            $
            (partial g)/(partial z) = (partial overline(g))/(partial overline(z)) = (partial overline(f))/(partial z) = -((partial F))/(partial overline(z)) = -(partial g)/(partial z) ~> (partial g)/(partial z) = ((partial F))/(partial overline z) = 0.
            $
            + 	 "(ii) $=>$ (iii)": Locally, if $omega|_U = f d z + g d overline z$, then $d'omega = 0$ implies $(partial g)/(partial z) = 0$, hence $g$ is anti-holomorphic on $U$, and $d''omega = 0$ implies $((partial F))/(partial overline z) = 0$, hence $f$ is holomorphic on $U$. 
            + 	 "(i)(ii) $=>$ (iv)": Since $omega$ is closed, locally $omega|_U = d f$ for some function $f$ on $U$. We have
            $
            d'omega = d'(d f) = d'(d' + d'')f = d'd''f = 0, 
            $
            hence $f$ is harmonic on $U$.
            + 	 "(iv) $=>$ (ii)": Locally, if $omega|_U = d f$ for some harmonic function $f$ on $U$, then $d'omega = d'(d f) = d'(d' + d'')f = d'd''f = 0$ and $d''omega = d''(d f) = d''(d' + d'')f = d''d'f = 0$.
        
     $qed$
]

#lemma[
    $
    cal(E)^(0,1)(X) = d'' cal(E)(X) xor overline omega(X),
    $
    where $xor$ is orthogonal direct sum with respect to the inner product defined above.
    
]

#proof[
        Suppose $f in cal(E)(X)$, $omega in omega(X)$, then
        $
        overline(omega) and *d''f = -i (overline(omega) and d'overline(f)) = -i overline(omega) and d overline f = i d(overline(f) overline(omega))
        $
        hence
        $
        chevron.l overline(omega), d''f chevron.r = integral.double_X d(overline(f) overline(omega)) = 0.
        $
        Therefore, $d'' cal(E)(X)$ is orthogonal to $overline omega(X)$. 

        Clearly $cal(E)^(0,1)(X) supset.eq d'' cal(E)(X) + overline omega(X)$. Since
        $
        H^1(X, cal(O)) = (cal(E)^(0,1)(X))/(d'' cal(E)(X)) ~> dim (cal(E)^(0,1)(X))/(d'' cal(E)(X)) = g = dim overline omega(X),
        $
        we have $cal(E)^(0,1)(X) = d'' cal(E)(X) xor overline omega(X)$.
     $qed$
]

#remark[
    Similarly, we can show that $cal(E)^(1,0)(X) = d' cal(E)(X) xor omega(X)$. 
]

#lemma[
    $
    d'cal(E)(X) xor d'' cal(E)(X) = d cal(E)(X) xor *d cal(E)(X).
    $
    
]

#proof[
        We have
        $
        d'f and *d''g = -i d'f and d'overline g = 0
        $
        and
        $
        d f and *(*d g) = -d f and d g = -d(f d g) ~> chevron.l d f, *d g chevron.r = -integral.double_X d(f d g) = 0,
        $
        hence $d'cal(E)(X) perp d'' cal(E)(X)$ and $d cal(E)(X) perp *d cal(E)(X)$.
        
        Clearly $d cal(E)(X) subset.eq d'cal(E)(X) xor d'' cal(E)(X)$ and $*d cal(E)(X) subset.eq d'cal(E)(X) xor d'' cal(E)(X)$. Write
        $
        d'f = (1)/(2) (d f + *d(-i overline(f))) in d cal(E)(X) xor *d cal(E)(X), \
        d''f = (1)/(2) (d f + *d(i overline(f))) in d cal(E)(X) xor *d cal(E)(X),
        $
        hence $d'cal(E)(X) xor d'' cal(E)(X) subset.eq d cal(E)(X) xor *d cal(E)(X)$.
     $qed$
]

#theorem[
    $
    cal L(X) := "ker" (cal(E)^((1))(X) xarrow(d) cal(E)^((2))(X)) = d cal(E)(X) xor "Harm" ^1(X).
    $
    
]

#proof[
        Clearly RHS is contained in LHS. Conversely, since $*d cal(E)(X)$, $d cal(E)(X)$ and $"Harm" ^1(X)$ are mutually orthogonal, it suffices to show that $cal L(X) perp *d cal(E)(X)$. Suppose $omega in cal L(X)$ and $f in cal(E)(X)$, then
        $
        omega and **d f = -omega and d f = d(f omega) ~> chevron.l omega, *d f chevron.r = integral.double_X d(f omega) = 0.
        $
     $qed$
]

#theorem[
    $
    cal(E)^((1))(X) = d cal(E)(X) xor *d cal(E)(X) xor "Harm"^1(X).
    $
    
]

#proof[
        By the previous two lemmas, we have
        $
        cal(E)^((1))(X) = d'cal(E)(X) xor d'' cal(E)(X) xor omega(X) xor overline omega(X) = d cal(E)(X) xor *d cal(E)(X) xor "Harm"^1(X).
        $
     $qed$
]

#theorem(name: "deRham-Hodge")[ 
    $
    H^1(X, CC) tilde.equiv "Rh" ^1(X) tilde.equiv "Harm" ^1(X).
    $
    
]

#proof[
        By the discussion before the definition of harmonic 1-forms, we have $H^1(X, CC) tilde.equiv "Rh" ^1(X)$. By the previous theorem, we have $cal L(X) = d cal(E)(X) xor "Harm" ^1(X)$, hence
        $
        "Rh"^1(X) = (cal L(X))/(d cal(E)(X)) tilde.equiv "Harm"^1(X).
        $
     $qed$
]

#proposition[
    If $sigma in "Harm" ^1(X)$ with $sigma = overline(sigma)$, i.e. $sigma$ is real, then exists a unique $omega in omega(X)$ such that $sigma = "Re" omega = (omega + overline(omega))/2$.
    
]

#proof[
        Write $sigma = omega_1 + overline(omega_2)$ for $omega_1, omega_2 in omega(X)$, then
        $
        sigma = overline sigma ~> omega_1 + overline(omega_2) = overline(omega_1) + omega_2 ~> omega_1 = omega_2 ~> sigma = "Re" (2 omega_1).
        $
        The uniqueness of $omega$ is straightforward since if $sigma = "Re" omega = "Re" omega'$, then $"Re" (omega - omega') = 0$, hence $omega - omega' = 0$ since $omega - omega' in omega(X)$.
     $qed$
]

#proposition[
    Let $X$ be a compact Riemann surface. If $sigma in "Harm" ^1(X)$ is exact, then $sigma = 0$. If $f in cal(E)(X)$ is harmonic, then $f$ is constant.
    
]

#proof[
        Since $d cal(E)(X) perp "Harm" ^1(X)$, if $sigma in "Harm" ^1(X)$ is exact, then $sigma perp sigma$, hence $sigma = 0$. Since $d f in d cal(E)(X) perp "Harm" ^1(X)$, if $f$ is harmonic, then $d f = 0$, hence $f$ is constant.
     $qed$
]

#proposition[
    Let $X$ be a compact Riemann surface and $sigma in "Harm" ^1(X)$. If for every closed curve $Gamma$ on $X$ (resp. $omega in omega(X)$), we have
    $
    integral_Gamma sigma = 0, ("resp. " "Re" (integral_Gamma omega) = 0),
    $
    then $sigma = 0$ (resp. $omega = 0$).
    
]

#proof[
        Since $sigma$ (resp. $"Re" omega$) is exact, the result follows from the previous theorem. 
     $qed$
]

== Jacobi Inversion Problem

#theorem(name: "Residue Theorem")[ 
    Let $X$ be a compact Riemann surface, $a_1, dots.h, a_n in X$ be distinct points and let $X' = X without \{ a_1, dots.h, a_n \}$. If $omega$ is a meromorphic 1-form on $X$ which is holomorphic on $X'$, then
    $
    sum_(k=1)^n "Re"s _(a_k)(omega) = 0.
    $
    
]

#proof[
        Pick disjoint charts $(U_k, z_k)$ around $a_k$ for every $k$ such that $z_k(a_k) = 0$ and $U_k tilde.equiv B_1(0)$. By partition of unity, exists $f_k in cal(E)(X)$ such that $0 <= f_k <= 1$, $"supp" (f_k) subset B_R (0) subset B_1(0)$ for some $R < 1$ and $f_k = 1$ on $B_epsilon (0)$ for some $0 < epsilon < R$. Since $omega in omega(X')$, $d omega = 0$ on $X'$. On $U_k' inter X'$, $f_k omega = omega$, hence
        $
        integral.double_X d(f_k omega) &= lim_(epsilon' -> 0) integral.double_(epsilon' <= |z| <= R) d(f_k omega) = integral_(|z| = R) f_k omega - lim_(epsilon' -> 0) integral_(|z| = epsilon') f_k omega \
        &= -lim_(epsilon' -> 0) integral_(|z| = epsilon') omega = -2pi i "Re"s_(a_k)(omega).
        $
        Let $g = 1 - sum_(k=1)^n f_k$, then $g in cal(E)(X)$, $0 <= g <= 1$ and $"supp" (g) subset X'$. Since $omega$ is holomorphic on $X'$, we have
        $
        integral.double_X d(g omega) = 0.
        $
        Therefore,
        $
        sum_(k=1)^n "Re"s_(a_k)(omega) &= -(1)/(2pi i) sum_(k=1)^n integral.double_X d(f_k omega) = -(1)/(2pi i) integral.double_X d(sum_(k=1)^n f_k omega) \
        &= -(1)/(2pi i) integral.double_X d((1-g)omega) = -(1)/(2pi i) integral.double_X d(omega - g omega) = 0.
        $
     $qed$
]

Let $X$ be a compact Riemann surface of genus $g >= 1$ and $omega_1, dots.h, omega_g$ be a basis of $omega(X)$. 

#definition[
    Let $C_1(X)$ be the free abelian group generated by all closed curves on $X$, i.e.
    $
    C_1(X) = \{ sum_(k=1 \}^n a_k Gamma_k | n in \Z_(>= 0), a_k in ZZ, Gamma_k " is a curve on " X " for every " k).
    $
    Define the boundary map $partial: C_1(X) -> "Div" (X)$ by $partial (Gamma) = Gamma(1) - Gamma(0)$ for every curve $Gamma$ on $X$, and extend $partial$ linearly to $C_1(X)$. Define the group of 1-cycles on $X$ to be
    $
    Z_1(X) = "ker" (C_1(X) xarrow(partial) "Div" (X)), 
    $
    and let $B_1(X)$ be the closed curves $Gamma$ on $X$ such that $integral_Gamma omega = 0$ for every $omega in omega(X)$. Define the first homology group of $X$ to be
    $
    H_1(X) = (Z_1(X))/(B_1(X)).
    $
]

#definition[
    Let $V$ be a $N$-dimensional complex vector space over $RR$. A lattice in $V$ is an additive subgroup $Gamma$ of $V$ such that $Gamma = ZZ Gamma_1 + dots + ZZ Gamma_N$ for some linearly independent vectors $Gamma_1, dots.h, Gamma_N$ in $V$.
]

#proposition[ [Lattice Criterion]
    $Gamma$ is a lattice in $V$ if and only if
    
        + $Gamma$ is discrete in $V$;
        + $Gamma subset.eq.not W$ for every proper subspace $W$ of $V$. 
    
    
]

#proof[
        Clearly a lattice satisfies (i) and (ii). 

        For the converse, we  proceed by induction on $N$. When $N = 0$ it's trivial. For $N > 0$, by (ii), $exists x_1, dots.h, x_N in Gamma$ which are linearly independent over $RR$. Let $V_1 = chevron.l x_1, dots.h, x_(N-1) chevron.r_RR$ and $Gamma_1 = Gamma inter V_1$. By induction hypothesis, $Gamma_1$ is a lattice in $V_1$, hence $exists Gamma_1, dots.h, Gamma_(N-1) in Gamma_1$ such that $Gamma_1 = ZZ Gamma_1 + dots + ZZ Gamma_(N-1)$. Also $Gamma_1, dots.h, Gamma_(N-1), x_N$ are linearly independent over $RR$. 
        
        Consider the parallelotope
        $
        P = \{ t_1 Gamma_1 + dots + t_(N-1 \} Gamma_(N-1) + t_N x_N | 0 <= t_i < 1 " for every " i).
        $
        For all $x in V$, we can uniquely write $x = c_1(x)Gamma_1 + dots + c_(N-1)(x)Gamma_(N-1) + c(x)x_N$ for some $c_i(x), c(x) in RR$. Pick
        $
        c(Gamma_N) = \min \{ c(x) | x in (Gamma inter P) without Gamma_1 \}.
        $
        Since $Gamma$ is discrete, the minimum is attained and $c(Gamma_N) > 0$. We claim that $Gamma = Gamma_1 + ZZ Gamma_N$. For all $x in Gamma$, exists $n in ZZ$ such that $c(x) = n c(Gamma_N) + Lambda$ for some $0 <= Lambda < c(Gamma_N)$ and $c_i(x) - n c_i(Gamma_N) = n_i + Lambda_i$ for some $n_i in ZZ$ and $0 <= Lambda_i < 1$ for every $i$. Then
        $
        x - n Gamma_N - sum_(i=1)^(N-1) n_i Gamma_i = sum_(i=1)^(N-1) Lambda_i Gamma_i + Lambda x_N in Gamma inter P
        $
        hence $Lambda = 0$, which implies that $x - n Gamma_N - sum_(i=1)^(N-1) n_i Gamma_i in Gamma_1$, hence $x in Gamma_1 + ZZ Gamma_N$. This shows that $Gamma$ is generated by $Gamma_1, dots.h, Gamma_(N-1), Gamma_N$, hence $Gamma$ is a lattice in $V$.
     $qed$
]

#definition[
    The period lattice of $X$ with respect to $omega_1, dots.h, omega_g$ is defined to be
    $
    Lambda = "Per" (omega_1, dots.h, omega_g) = \{ (integral_Gamma omega_1, dots.h, integral_Gamma omega_g) | Gamma in H_1(X) \} subset.eq CC^g.
    $
    The Jacobi variety of $X$ is defined to be $"Jac" (X) = CC^g/Lambda$.
]

#theorem[
    $Gamma$ is a lattice in $CC^g tilde.equiv RR^(2g)$. 
    
]

#proof[
        We first show that there exists distinct $a_1, dots.h a_g$ in $X$ such that for all $omega in (X)$, if $omega(a_1) = dots = omega(a_g) = 0$, then $omega = 0$. For $a in X$, define
        $
        H_a := \{ omega in omega(X) | omega(a) = 0 \},
        $
        then either $H_a = omega(X)$ or $"codim" H_a = 1$. Sine $inter.big_(a in X) H_a = \{ 0 \}$, we can find $a_1 in X$ such that $H_(a_1) != omega(X)$, then find $a_2 in X$ such that $H_(a_1) inter H_(a_2) != H_(a_1)$, and so on, until we find $a_1, dots.h, a_g$ such that $inter.big_(k=1)^g H_(a_k) = \{ 0 \}$.

        Let $omega_1, dots.h, omega_g$ be a basis of $omega(X)$. Find disjoint charts $(U_k, z_k)$ around $a_k$ for every $k$ such that $z_k(a_k) = 0$ and $U_k tilde.equiv B_1(0)$. Locally write $omega_i|_(U_j) = phi.alt_(i j) d z_j$ for some holomorphic function $phi.alt_(i j) in cal(O)(U_j)$. Consider the matrix $A = (phi.alt_(i j)(a_j))_(1 <= i, j <= g)$, then $A$ is full-rank since $\{ omega_i \}$ is a basis of $omega(X)$ and $inter.big_(k=1)^g H_(a_k) = \{ 0 \}$. Define a map
        $
        F: U_1 times dots times U_g -> CC^g, quad  (x_1, dots.h, x_g) |-> (sum_(j=1)^g integral_(a_j)^(x_j) omega_1, dots.h, sum_(j=1)^g integral_(a_j)^(x_j) omega_g).
        $
        The integral is independent of the choice of path since $U_j$ is simply connected for every $j$. The Jacobian matrix of $F$ at $(a_1, dots.h, a_g)$ is $((partial F_i)/(partial z_j))_(1 <= i, j <= g) = A$, which is invertible, hence $F$ is a local biholomorphism around $(a_1, dots.h, a_g)$. Therefore, there exists an open neighborhood $V$ of $0$ in $CC^g$ such that $F$ induces a biholomorphism between $V$ and an open neighborhood of $(a_1, dots.h, a_g)$ in $X^g$. We claim that $Gamma inter V = \{ 0 \}$. If not, say $F(x_1, dots.h, x_g) in Gamma inter (V without \{ 0 \})$ for some $(x_1, dots.h, x_g) in U_1 times dots times U_g$. Suppose that after reindexing, $x_j != a_j$ for $j = 1, dots.h, k$ and $x_j = a_j$ for $j = k+1, dots.h, g$. By Abel's theorem, exists a meromorphic function $f$ on $X$ such that $(f) = x_1 + dots + x_k - a_1 - dots - a_k$, i.e. $"Re"s _(a_j)(f) = c_j != 0$ for $j = 1, dots.h, k$. By Residue theorem, 
        $
        0 = "Re"s (f omega_i) = sum_(j=1)^k "Re"s _(a_j)(f omega_i) = sum_(j=1)^k c_j phi.alt_(i j)(a_j),
        $
        which implies that $A (c_1, dots.h, c_k)^T = 0$, contradicting the invertibility of $A$. Therefore, $Gamma inter V = \{ 0 \}$, which implies that $Gamma$ is discrete in $CC^g$. If $Gamma$ is contained in a proper subspace $W$ of $CC^g$, say
        $
        W = \{ (x_1, y_1, dots.h, x_g, y_g) in RR^(2g \} | sum_(j=1)^g r_j x_j + r_j' y_j = 0)
        $
        for some $r_j, r_j' in RR$ not all zero. Note that
        $
        0 &= sum_(j=1)^g r_j x_j + r_j' y_j \
        &= "Re" (sum_(j=1)^g (r_j - i r_j') (x_j + i y_j)) \
        &= "Re" (sum_(j=1)^g (r_j - i r_j') integral_Gamma omega_j) \
        &= "Re" (integral_Gamma sum_(j=1)^g (r_j - i r_j') omega_j)
        $
        for every $Gamma in H_1(X)$. By the previous proposition, $sum_(j=1)^g (r_j - i r_j') omega_j = 0$, which implies that $r_j = r_j' = 0$ for every $j$, contradicting the choice of $r_j, r_j'$. Therefore, $Gamma$ is not contained in any proper subspace of $CC^g$. By the lattice criterion, $Gamma$ is a lattice in $CC^g$.
     $qed$
]

#definition[
    Let $"Div" _p(X)$ be the group of principal divisors on $X$, and $"Div" _0(X)$ be the group of degree zero divisors on $X$. Define the Picard group of $X$ to be
    $
    "Pic" (X) = ("Div" (X))/("Div" _p(X)), 
    $
    and
    $
    "Pic" _0(X) = ("Div" _0(X))/("Div" _p(X)). 
    $
    We have a short exact sequence of abelian groups
    $
    0 -> "Pic" _0(X) -> "Pic" (X) xarrow("deg") ZZ -> 0. 
    $
]

#definition[
    For any divisor $D$ on $X$ with degree zero, we can find a closed curve $Gamma$ on $X$ such that $partial Gamma = D$ by connecting the points in $D$ by curves. Define a map $phi: "Div" _0(X) -> "Jac" (X)$ by
    $
    phi(D) = (integral_Gamma omega_1, dots.h, integral_Gamma omega_g) + Lambda.
    $
    We can verify that $phi$ is well-defined since if $Gamma'$ is another closed curve such that $partial Gamma' = D$, then $Gamma - Gamma' in Z_1(X)$, hence $integral_(Gamma - Gamma') omega_k in Lambda$ for every $k$, which implies that $integral_Gamma omega_k + Lambda = integral_(Gamma') omega_k + Lambda$ for every $k$. 
]

Note that $D in "ker" phi$ if and only if there exists a closed curve $Gamma$ on $X$ such that $partial Gamma = D$ and $integral_Gamma omega_k = 0$ for every $k$. 

#theorem(name: "Abel's Theorem")[ 
    Let $X$ be a compact Riemann surface and $D$ be a divisor of degree zero on $X$. Then there exists a meromorphic function $f$ on $X$ such that $D = (f)$ if and only if there exists a closed curve $Gamma in C_1(X)$ such that $partial Gamma = D$ and $integral_Gamma omega = 0$ for every $omega in omega(X)$. 
]

By Abel's theorem, we have $"ker" phi = "Div" _p(X)$, hence $phi$ induces an injective homomorphism $j: "Pic" _0(X) -> "Jac" (X)$. In fact, $j$ is also surjective, hence an isomorphism $"Pic" _0(X) tilde.equiv "Jac" (X)$, which is the moduli space of degree zero line bundles on $X$.

#theorem[
    $j: "Pic" _0(X) -> "Jac" (X)$ is surjective. 
    
]

#proof[
        For all $p in "Jac" (X)$, we can find $xi in CC^g$ such that $p = xi + Lambda$. Let $N >> 0$ such that $(1)/(N) xi in V$, where $V$ is the open neighborhood of $0$ in $CC^g$ such that $F$ induces a biholomorphism between $V$ and an open neighborhood of $(a_1, dots.h, a_g)$ in $X^g$. Then we can find $(x_1, dots.h, x_g) in U_1 times dots times U_g$ and curves $Gamma_j in U_j$ connecting $a_j$ and $x_j$ for every $j$ such that
        $
        (integral_c omega_1, dots.h, integral_c omega_g) = (1)/(N) xi,
        $
        where $c = sum_(j=1)^g Gamma_j$, thus $D = partial C$ is a divisor of degree zero such that $phi(D) = (1)/(N) xi + Lambda$. Let $theta = N D + "Pic" _p(X)$, then $phi(theta) = xi + Lambda = p$, which implies that $j(theta) = p$. Therefore, $j$ is surjective.
     $qed$
]

Fix $a_1, dots.h, a_g in X$ and define
$
psi: X^g -> "Pic" _0(X), quad  (x_1, dots.h, x_g) |-> [x_1 + dots + x_g - a_1 - dots - a_g].
$
By the isomorphism $j: "Pic" _0(X) -> "Jac" (X)$, this induces a holomorphic map $J: X^g -> "Jac" (X)$, defined by
$
J(x_1, dots.h, x_g) = (sum_(k=1)^g integral_(a_k)^(x_k) omega_1, dots.h, sum_(k=1)^g integral_(a_k)^(x_k) omega_g) + Lambda.
$
To show that $J$ is surjective, it suffices to show that $psi$ is surjective. Let $D$ be a divisor of degree zero on $X$. Consider $D' = D + a_1 + dots + a_g$, then $"deg" D' = g$. By Riemann-Roch theorem, we have $ell (D') = g$, hence $h^0(X, cal(O)_(D')) >= 1$, which implies that there exists a meromorphic function $f in cal(M)(X)$ such that $(f) + D' >= 0$, i.e. $(f) + D' = x_1 + dots + x_g$ for some $x_1, dots.h, x_g in X$. Therefore, $psi(x_1, dots.h, x_g) = [D]$, which implies that $psi$ is surjective.

#example[
    When $g = 1$, then $J$ is an isomorphism: if $x in "ker" J$, then there exists $f in cal(M)(X)$ such that $(f) = x - a_1$, hence $f: X -> PP^1$ sending $a$ to $oo$, which is an isomorphism, contradiction. Therefore, $J$ is injective, hence $J$ is an isomorphism, so $"Jac" (X) tilde.equiv CC/Lambda$ is a torus. 
]

== Abel's Theorem

Recall that $C_1(X)$ is the free abelian group generated by all closed curves on $X$, and $partial: C_1(X) -> "Div" (X)$ is the boundary map defined by $partial (Gamma) = Gamma(1) - Gamma(0)$ for every curve $Gamma$ on $X$.

#definition[
    Let $X$ be a Riemann surface and $D in "Div" (X)$ and
    $
    X_D := \{ x in X | D(x) >= 0 \}.
    $
    We say that $f in cal(E)(X_D)$ is a weak solution of $D$ if for all $a in X$, there exists a chart $(U, z)$ with $z(a) = 0$ and $psi in cal(E)(U)$ with $psi(a) != 0$ such that $f = psi z^k$ on $U inter X_D$, where $k = D(a)$. 
]

A weak solution is weak in the sense that it may not be a meromorphic function on $X$ since it is only partialerentiable on $X_D$. 

#proposition[
    Let $D = sum_(i=1)^n k_i a_i$ be a divisor on $X$ with $k_i in ZZ$ and $a_i in X$ distinct for every $i$. If $f$ is a weak solution of $D$, then for all $g in cal(E)(X)$, we have
    $
    (1)/(2pi i) integral.double_X (d f)/(f) and d g = sum_(i=1)^n k_i g(a_i).
    $
    
]

#proof[
        Choose disjoint charts $(U_j, z_j)$ around $a_j$ for every $j$ such that $z_j(a_j) = 0$ and $U_j tilde.equiv B_1(0)$ such that $f = psi_j z_j^(k_j)$ with $psi_j in cal(E)(U_j)$ and $psi_j(x) != 0$ for every $x in U_j$. 

        Suppose $0 < r < r' < 1$. Exists $phi.alt_j in cal(E)(X)$ such that $"supp" (phi.alt_j) subset B_(r')(0)$ and $phi.alt_j = 1$ on $B_r(0)$ for every $j$. Let $g_j = phi.alt_j g in cal(E)(X)$, then
        $
        integral.double_(U_j) (d f)/(f) and d g_j &= integral.double_(U_j) (k_j (d z_j)/(z_j) + (d psi_j)/(psi_j)) and d g_j \
        &= integral.double_(U_j) k_j (d z_j)/(z_j) and d g_j + integral.double_(U_j) (d psi_j)/(psi_j) and d g_j \
        &= integral.double_(U_j) k_j (d z_j)/(z_j) and d g_j - integral.double_(U_j) d(g_j (d psi_j)/(psi_j)) \
        &= integral.double_(U_j) k_j (d z_j)/(z_j) and d g_j = -lim_(epsilon -> 0) k_j integral.double_(epsilon <= |z_j| <= r') d(g_j (d z_j)/(z_j)) \
        &= lim_(epsilon -> 0) k_j integral_(|z_j| = epsilon) g_j (d z_j)/(z_j) = 2pi i k_j g(a_j).
        $
        Set $g_0 = g - sum_(j=1)^n g_j$, then $g_0|_(|z
        j| <= r) = 0$ for every $j$, hence $"supp" (g_0)$ is compact in $X' = X without \{ a_1, dots.h, a_n \}$. Therefore, $g_0$ can be extended to a smooth function on $X$ with compact support in $X'$, so
        $
        integral.double_X (d f)/(f) and d g &= integral.double_(X) (d f)/(f) and d g_0 + sum_(j=1)^n integral.double_(U_j) (d f)/(f) and d g_j \
        &= -integral.double_X d(g_0 (d f)/(f)) + 2pi i sum_(j=1)^n k_j g(a_j) = 2pi i sum_(j=1)^n k_j g(a_j).
        $
     $qed$
]

#lemma(id: "lm:weak-solution-of-boundary")[
    Let $c: [0, 1] -> X$ be a curve on $X$ and $U subset.double X$ with $c([0, 1]) subset U$. Then exists a weak solution $f$ of $partial c$ with $f|_(X without U) equiv 1$ such that for all $omega in cal(E)^((1))(X)$ with $d omega = 0$, we have
    $
    integral_c omega = (1)/(2pi i) integral.double_X (d f)/(f) and omega.
    $
]
#proof[
        Suppose that $U tilde.equiv B_1(0) subset.eq CC$. Let $a = c(0)$ and $b = c(1)$. Let $c([0, 1]) subset B_r(0)$ for some $r < 1$. Note that $(z - a)/(z - b)$ is nowhere vanishing holomorphic function on $\{ r < |z| < 1 \}$, hence exists a well-defined holomorphic branch of $log (z - a)/(z - b)$ on $\{ r < |z| < 1 \}$. Choose $psi in cal(E)(U)$ such that $psi = 1$ on $B_r(0)$ and $"supp" (psi) subset B_(r')(0)$ for some $r < r' < 1$. Define
        $
        f(z) = cases(
            "exp" (psi(z) log (z - a)/(z - b)), r < |z| < 1,
            (z - a)/(z - b), |z| <= r,
            1, |z| >= r',
        )
        $
        which is a weak solution of $partial c$ since $f(z) = psi(z) (z - a)/(z - b)$ on $U$ and $f(z) = 1$ on $X without U$. For $omega = cal(E)^((1))(X)$ with $d omega = 0$, let $omega|_U = d h$ for some $h in cal(E)(U)$. Choose $phi.alt in cal(E)(X)$ such that $phi.alt = 1$ on $B_r'(0)$ and $"supp" (phi.alt) subset B_(r'')(0)$ for some $r' < r'' < 1$. Then $g = phi.alt h in cal(E)(X)$ and $omega = d g$ on $\{ |z| <= r' \}$, hence
        $
        (1)/(2pi i) integral.double_X (d f)/(f) and omega = (1)/(2pi i) integral.double_(|z| <= r') d(g (d f)/(f)) = g(b) - g(a) = integral_c omega.
        $

        In general, by compactness of $c([0, 1])$, we can find a partition $0 = t_0 < t_1 < dots < t_n = 1$ such that $c([t_(j-1), t_j]) subset U_j$ for some $U_j tilde.equiv B_1(0)$ for every $j$. Let $c_j = c|_([t_(j-1), t_j])$ for every $j$. By the previous case, exists a weak solution $f_j$ of $partial c_j$ with $f_j|_(X without U_j) equiv 1$ such that for all $omega in cal(E)^((1))(X)$ with $d omega = 0$, we have
        $
        integral_(c_j) omega = (1)/(2pi i) integral.double_X (d f_j)/(f_j) and omega.
        $
        Let $f = product_(j=1)^n f_j$, then $f$ is a weak solution of $sum_(j=1)^n partial c_j = partial c$ with $f|_(X without union.big_(j=1)^n U_j) equiv 1$ such that for all $omega in cal(E)^((1))(X)$ with $d omega = 0$, we have
        $
        integral_c omega = sum_(j=1)^n integral_(c_j) omega = sum_(j=1)^n (1)/(2pi i) integral.double_X (d f_j)/(f_j) and omega = (1)/(2pi i) integral.double_X (d f)/(f) and omega.
        $
     $qed$
]

#theorem[
    Let $X$ be a compact Riemann surface, $D in "Div" (X)$ with $"deg" D = 0$. Then $D$ has a solution if and only if there exists a $1$-chain $c in C_1(X)$ with $partial c = D$ such that $integral_c omega = 0$ for every $omega in omega(X)$.
    
]

#proof[
        
        "$<=$": Let $c = sum_(j=1)^k n_j c_j$ for some $n_j in ZZ$ and curves $c_j$ on $X$ for every $j$. By the previous lemma, exists weak solutions $f_j$ of $partial c_j$ with $f_j|_(X without U_j) equiv 1$ for some $U_j subset.double X$ such that for all $omega in cal(E)^((1))(X)$ with $d omega = 0$, we have
        $
        integral_(c_j) omega = (1)/(2pi i) integral.double_X (d f_j)/(f_j) and omega.
        $
        Let $f = product_(j=1)^k f_j^(n_j)$, then $f$ is a weak solution of $partial c = D$ with $f|_(X without union.big_(j=1)^k U_j) equiv 1$ such that for all $omega in cal(E)^((1))(X)$ with $d omega = 0$, we have
        $
        integral_c omega = sum_(j=1)^k n_j integral_(c_j) omega = sum_(j=1)^k n_j (1)/(2pi i) integral.double_X (d f_j)/(f_j) and omega = (1)/(2pi i) integral.double_X (d f)/(f) and omega.
        $
        Since $integral_c omega = 0$ for every $omega in omega(X)$, we have $integral.double_X (d f)/(f) and omega = 0$ for every $omega in omega(X)$. Note that
        $
        0 = integral.double_X (d f)/(f) and omega = integral.double_X (d'f + d''f)/(f) and omega = integral.double_X (d''f)/(f) and omega. 
        $
        Recal that $cal(E)^((0, 1))(X) = d''cal(E)(X) xor overline(omega)(X)$, hence the above equation implies that $chevron.l (d''f)/(f), -*omega chevron.r = chevron.l (d''f)/(f), -i overline(omega) chevron.r = 0$ for every $omega in omega(X)$, which implies that $(d''f)/(f) = d''g$ for some $g in cal(E)(X)$, hence $f e^(-g)$ is a meromorphic function on $X$ with $(f e^(-g)) = D$, which implies that $D$ has a solution.

        "$=>$": If $D = 0$, then we can take $c = 0$. If $D != 0$ and $D = (f)$ for some $f in cal(M)(X)$. For each holomorphic $1$-form $omega$ on $X$ and $V subset.eq PP^1$ with $f^(-1)(V) = union.sq.big_(j=1)^n U_j$ and $phi.alt_j: U_j -> V$ is a biholomorphism for every $j$, define
        $
        "Trace" (omega)|_V = sum_(j=1)^n phi.alt_j^* omega.
        $
        Then $"Trace" (omega)$ is a well-defined holomorphic $1$-form on $Y$, where $Y$ equals $PP^1$ excluding the critical values of $f$. By extension theorem on $PP^1$, $"Trace" (omega)$ can be extended to a holomorphic $1$-form on $PP^1$, which must be zero since $omega(PP^1) = \{ 0 \}$. Therefore, $"Trace" (omega) = 0$, which implies that $sum_(f(x) = y) omega(x) = 0$ for every $y in PP^1$. Let $c$ be the curve on $X$ defined by $c(t) = f^(-1)(e^(2pi i t))$ for every $t in [0, 1]$, then $partial c = (f)$ and $integral_c omega = integral_0^1 sum_(f(x) = e^(2pi i t)) omega(x) d t = 0$ for every $omega in omega(X)$.
     $qed$
]

= Non-compact Riemann Surfaces

== Weyl's Lemma

#definition[
    Given an open set $X subset.eq CC$, define
    $
    cal(D)(X) = \{ f in cal(E)(X) : f " has compact support in " X \}.
    $
    For $(f_n) subset.eq cal(D)(X)$, we say that $f_n -> f$ in $cal(D)(X)$ if there exists a compact set $K subset.eq X$ such that $"supp" (f_n) subset.eq K$ for $n$ sufficiently large and $"supp" (f) subset.eq K$ and $D^alpha f_n -> D^alpha f$ uniformly on $K$ for every multi-index $alpha = (alpha_1, alpha_2) in NN^2$. Denote by $f_n xarrow(cal(D)) f$ if $f_n -> f$ in $cal(D)(X)$.
]

#definition[
    A distribution on $X$ is a continuous linear mapping
    $
    T: cal(D)(X) -> CC, quad  f |-> T[f].
    $
    Continuous in the sense that if $f_n xarrow(cal(D)) f$, then $T[f_n] -> T[f]$. Let $cal(D)'(X)$ be the collection of all distributions on $X$. 
]

Given a continuous function $h in cal C(X)$, we can define a distribution $T_h$ by
$
T_h [f] = integral_X h(z) f(z) d x d y
$
with $z = x + i y$ for every $f in cal(D)(X)$. We show that $f |-> T_f$ is an embedding of $cal C(X)$ into $cal(D)'(X)$. Suppose that $T_h = 0$, i.e. $integral.double_X h(z) f(z) d x d y = 0$ for every $f in cal(D)(X)$. If $h(a) != 0$ for some $a in X$, then we can find a neighborhood $U$ of $a$ such that $"Re" h(z) > 0$ for every $z in U$. Choose $phi.alt in cal(D)(X)$ with $"supp" phi.alt subset U$ and $0 <= phi.alt <= 1$ such that $phi.alt|_A equiv 1$ for some neighborhood $A$ of $a$, then
$
T_h [phi.alt] = integral.double_X h(z) phi.alt(z) d x d y = integral.double_A h(z) d x d y + integral.double_(U without A) h(z) phi.alt(z) d x d y > 0,
$
contradiction. Therefore, $h(a) = 0$ for every $a in X$, hence $h = 0$. Therefore, $f |-> T_f$ is an embedding of $cal C(X)$ into $cal(D)'(X)$, so we can view $cal(D)'(X)$ as an extension of continuous functions on $X$.

Observe that for $h in cal(E)(X)$, $f in cal(D)(X)$, by integration by parts, we have
$
integral.double_X h(z) ((partial F))/(partial x)(z) d x d y = -integral.double_X (partial h)/(partial x)(z) f(z) d x d y \
integral.double_X h(z) ((partial F))/(partial y)(z) d x d y = -integral.double_X (partial h)/(partial y)(z) f(z) d x d y. 
$
More generally, 
$
integral.double_X h(z) D^alpha f(z) d x d y = (-1)^(|alpha|) integral.double_X D^alpha h(z) f(z) d x d y, 
$
where $alpha = (alpha_1, alpha_2) in NN^2$ is a multi-index and $|alpha| = alpha_1 + alpha_2$. Therefore, for $T in cal(D)'(X)$, we can define $D^alpha T$ by
$
(D^alpha T)[f] := (-1)^(|alpha|) T[D^alpha f]
$
for every $f in cal(D)(X)$, which is a distribution since if $f_n xarrow(cal(D)) f$, then $D^alpha f_n xarrow(cal(D)) D^alpha f$. 

#proposition[
    There exists $rho in cal(D)(CC)$ such that
    
    + $"supp" (rho) subset.eq B_1(0)$;
    + $rho(z) = rho(|z|)$ for every $z in CC$;
    + $integral.double_CC rho(x + i y) d x d y = 1$.
    
    
]

#proof[
        Let $phi.alt_0 in cal(E)(RR)$ such that $"supp" (phi.alt_0) subset.eq (-1, 1)$ and $phi.alt_0(x) = phi.alt_0(-x)$ for every $x in RR$ and $phi.alt_0|_([-1/2, 1/2]) equiv 1$. Define $phi.alt(z) = phi.alt_0(z)$ on $CC$, and then define
        $
        rho(z) = (phi.alt(z))/(integral.double_CC phi.alt(x + i y) d x d y).
        $
        Then $rho$ satisfies the required properties.
     $qed$
]

For $epsilon > 0$, define $rho_epsilon (z) = (1)/(epsilon^2) rho((z)/(epsilon))$ for every $z in CC$. Then $rho_epsilon$ also satisfies the properties in the previous proposition, and $"supp" (rho_epsilon) subset.eq B_epsilon (0)$ for every $epsilon > 0$.

Define
$
X^((epsilon)) = \{ z in X | overline(B_epsilon (z)) subset.eq X \}
$
is an open subset of $X$ for every $epsilon > 0$. For $f in cal C(X)$, define the smoothing of $f$ on $X^((epsilon))$ by
$
("sm"_epsilon f)(z) = integral.double_X rho_epsilon (z - zeta) f(zeta) d xi d eta
$
for every $z in X^((epsilon))$ with $zeta = xi + i eta$. Note that $"sm"_epsilon f$ is well-defined since $"supp" (rho_epsilon (z - dot)) subset.eq B_epsilon (z) subset.eq X$ for every $z in X^((epsilon))$. Moreover, $"sm"_epsilon f$ is partialerentiable on $X^((epsilon))$ since we can partialerentiate under the integral sign, so
$
(d)/(d z) ("sm"_epsilon f)(z) = integral.double_X (d)/(d z) rho_epsilon (z - zeta) f(zeta) d xi d eta. 
$

Note that
$
"sm"_epsilon f(z) &= integral.double_X rho_epsilon (z - zeta) f(zeta) d xi d eta = integral.double_(|z - zeta| < epsilon) rho_epsilon (z - zeta) f(zeta) d xi d eta \
(w = z - zeta = u + i v) quad &= integral.double_(|w| < epsilon) rho_epsilon (w) f(z - w) d u d v = integral.double_X rho_epsilon (w) f(z - w) d u d v, 
$
as $epsilon -> 0$ and $w -> 0$, $f(z - w) -> f(z)$, hence $"sm"_epsilon f(z) -> f(z)$ for every $z in X$. 

Write
$
("sm"_epsilon f)(z) &= integral.double_(|zeta - z| < epsilon) rho_epsilon (z - zeta) f(zeta) d xi d eta \
&= integral.double_(|zeta - z| < epsilon) rho_epsilon (zeta - z) f(zeta) d xi d eta = integral.double_(|w| < epsilon) rho_epsilon (w) f(z + w) d u d v \
=> D^alpha ("sm"_epsilon f)(z) &= integral.double_(|w| < epsilon) rho_epsilon (w) D^alpha f(z + w) d u d v, \
&= integral.double_(|zeta - z| < epsilon) rho_epsilon (z - zeta) D^alpha f(zeta) d xi d eta = "sm"_epsilon (D^alpha f)(z).
$

#proposition[
    For $z in X^((epsilon))$, if $f$ is harmonic on $B_epsilon (z)$, then $"sm"_epsilon f(z) = f(z)$.
    
]

#proof[
        For $0 <= r < epsilon$, by Mean Value Property, we have
        $
        f(z) = (1)/(2pi) integral_0^(2pi) f(z + r e^(i theta)) d theta.
        $
        Therefore,
        $
        ("sm"_epsilon f)(z) &= integral.double_(|w| < epsilon) rho_epsilon (w) f(z + w) d u d v \
        &= limits(integral.double)_(0 <= r < epsilon \ 0 <= theta < 2pi) rho_epsilon (r e^(i theta)) f(z + r e^(i theta)) r d r d theta \
        &= integral_0^epsilon rho_epsilon (r) ((1)/(2pi) integral_0^(2pi) f(z + r e^(i theta)) d theta) r d r \
        &= integral_0^epsilon rho_epsilon (r) f(z) r d r \
        &= f(z) integral_0^epsilon rho_epsilon (r) r d r = f(z).
        $
     $qed$
]

#theorem(name: "Weyl's Lemma")[ 
    If $T in cal(D)'(X)$ and $delta T = (partial^2/partial x^2 + partial^2/partial y^2) T = 0$, then $T$ is a smooth function on $X$, i.e. there exists $h in cal(E)(X)$ such that $T = T_h$.
    
]

#proof[
        For $epsilon > 0$ and $z in X^((epsilon))$, define
        $
        h(z) = T[rho_epsilon (dot - z)]. 
        $
        We have
        $
        (partial h)/(partial x)(z) &= lim_(delta x -> 0) (1)/(delta x) (T_zeta [g(zeta, x + delta x + i y)] - T_zeta [g(zeta, x + i y)]) \
        &= lim_(delta x -> 0) T_zeta [(g(zeta, x + delta x + i y) - g(zeta, x + i y))/(delta x)]. 
        $
        Define
        $
        f_(delta x)(zeta) = (g(zeta, x + delta x + i y) - g(zeta, x + i y))/(delta x),
        $
        then $f_(delta x) in cal(D)(X)$ for every $delta x$ sufficiently small and $f_(delta x) xarrow(cal(D)) (partial)/(partial x) rho_epsilon (dot - z)$ as $delta x -> 0$, hence
        $
        (partial h)/(partial x)(z) = lim_(delta x -> 0) T_zeta[f_(delta x)(zeta)] = T_zeta[(partial)/(partial x) rho_epsilon (zeta - z)].
        $
        Similarly, we have
        $
        (partial h)/(partial y)(z) = T_zeta[(partial)/(partial y) rho_epsilon (zeta - z)], 
        $
        so $h(z) in cal(E)(X^((epsilon)))$. 

        We claim that $T["sm"_epsilon f] = integral.double_(X^((epsilon))) h(z) f(z) d x d y$ for every $f in cal(D)(L)$ with $L subset.double X^((epsilon))$. Since $rho_epsilon (zeta - z) f(z)$ has compact suppport, pick a rectangle $R$ such that $"supp" (rho_epsilon (zeta - dot) f) subset.eq R$. Partition $R$ into $n^2$ small rectangles $R_1, dots.h, R_(n^2)$ of equal size and $z_k$ be the center of $R_k$ for every $k$. Let
        $
        G_n(zeta) = (|R|)/(n^2) sum_(k=1)^(n^2) rho_epsilon (zeta - z_k) f(z_k),
        $
        then $G_n in cal(D)(X)$ for every $n$ and $G_n xarrow(cal(D)) integral.double_X rho_epsilon (zeta - z) f(z) d x d y = ("sm"_epsilon f)(zeta)$ as $n -> oo$, hence
        $
        T[integral.double_X rho_epsilon (dot - z) f(z) d x d y] &= lim_(n -> oo) T[G_n] \
        &= lim_(n -> oo) (|R|)/(n^2) sum_(k=1)^(n^2) T[rho_epsilon (dot - z_k)] f(z_k) \
        &= integral.double_(X^((epsilon))) h(z) f(z) d x d y.
        $

        Recall Dolbeault's lemma, for $X = B_R (0)$ and $g in cal(E)(X)$, we can find $f in cal(E)(X)$ such that $((partial F))/(partial overline(z)) = g$. Since $delta = partial^2/partial x^2 + partial^2/partial y^2 = 4 partial^2/partial z partial overline(z)$, we can also find $f in cal(E)(X)$ such that $delta f = g$ for every $g in cal(E)(X)$. 

        Now, we claim that $T[f] = T["sm"_epsilon f]$ for every $f in cal(D)(X)$. By Dolbeault's lemma, there exists $psi in cal(E)(CC)$ such that $delta psi = f$. Note that $delta psi = 0$ on $V := CC without "supp" f$, i.e. harmonic on $V$, hence $psi = "sm"_epsilon psi$ on $V^((epsilon))$, so $phi.alt := psi - "sm"_epsilon psi$ has compact support in $CC$, so $phi.alt in cal(D)(X)$. Therefore,
        $
        0 = delta T[phi.alt] = T[delta phi.alt] = T[delta psi - delta ("sm"_epsilon psi)] = T[f - "sm"_epsilon f].
        $
        Therefore, $T[f] = T["sm"_epsilon f]$ for every $f in cal(D)(X)$, hence $T = T_h$ on $X^((epsilon))$. Since $epsilon > 0$ is arbitrary, we have $T = T_h$ on $X$, so $T$ is a smooth function on $X$.
     $qed$
]

#lemma[
    If $(partial T)/(partial overline(z)) = 0$, then $T$ is a holomorphic function on $X$. 
    
]

#proof[
        Since $(partial T)/(partial overline(z)) = 0$, we have
        $
        delta T = 4 (partial^2 T)/(partial z partial overline(z)) = 0,
        $
        hence $T$ is a smooth function on $X$ by Weyl's lemma, and thus $T in cal(O)(X)$. 
     $qed$
]

== Countable Topology

Note that if $X$ is compact, then $X$ is second countable. 

#lemma(name: "Poincaré-Volterra")[
    Suppose $Z'$ is a connected manifold, $Z$ is a Hausdorff space with countable topology and $f: Z' -> Z$ is a continuous discrete mapping, then $Z'$ has countable topology.
]
#proof[
    Let $frak(U)$ be a countable basis of the topology of $Z$. Let $frak(V)$ be the collection of all open subsets $V$ of $Z'$ such that
    
        + 	 $V$ is a connected component of $f^(-1)(U)$ for some $U in frak(U)$;
        + 	 $V$ has countable topology.
    

    We claim that $frak(V)$ is a basis of the topology of $Z'$. Let $x in Z'$ and $D$ be an open neighborhood of $x$ in $Z'$. Since $f^(-1)(f(x))$ is discrete, exists $x in W subset.double D$ such that $partial W inter f^(-1)(f(x)) = emptyset$ and $W inter f^(-1)(f(x)) = \{ x \}$. Also, $f(partial W)$ is compact in $Z$ with $f(x) in.not f(partial W)$, hence exists $U in frak(U)$ such that $f(x) in U$ and $U inter f(partial W) = emptyset$. Let $V$ be the connected component of $f^(-1)(U)$ containing $x$, then $V subset.eq W$. Since $overline(W)$ is compact, it has countable topology, hence $V$ has countable topology, so $V in frak(V)$. Therefore, $frak(V)$ is a basis of the topology of $Z'$. 

    We now claim that $frak(V)$ is countable. Fix $V^* in frak(V)$. For $n in NN$, define
    $
    frak(V)_n = \{ V in frak(V) : exists V^* = V_0, V_1, dots.h, V_n = V " in " frak(V) " such that " V_(j-1 \} inter V_j != emptyset " for every " j). 
    $
    Fix $x_0 in V^*$, for $x in V in frak(V)$, let $c: [0, 1] -> Z'$ be a curve from $x_0$ to $x$, then since $[0, 1]$ is compact, exists a partition $0 = t_0 < t_1 < dots < t_n = 1$ such that $c([t_(j-1), t_j]) subset.eq V_j$ for some $V_j in frak(V)$ for every $j$, hence $V in frak(V)_n$. Therefore, $frak(V) = union.big_(n=0)^oo frak(V)_n$. 

    We now claim that for every $V_0 in frak(V)$, there exists at most countably many $V in frak(V)$ such that $V inter V_0 != emptyset$. For all $U in frak(U)$, the connected components of $f^(-1)(U)$ are pairwise disjoint. Since $V_0$ has a countable topology, $exists$ at most countably many $V$ which are connected components of $f^(-1)(U)$ such that $V inter V_0 != emptyset$: otherwise, if there are uncountably many, then $V_0$ has uncountable many disjoint open subsets, contradicting that $V_0$ has countable topology. Since $frak(U)$ is countable, there are at most countably many $V in frak(V)$ such that $V inter V_0 != emptyset$.
    
    We then show that $frak(V)_n$ is countable for every $n$. Proceed by induction on $n$. For $n = 0$, $frak(V)_0 = \{ V^* \}$ is countable. Suppose that $frak(V)_(n-1)$ is countable for some $n >= 1$. For $V in frak(V)_n$, there exists $V' in frak(V)_(n-1)$ such that $V inter V' != emptyset$, hence there are at most countably many $V$ such that $V inter V' != emptyset$ for every $V' in frak(V)_(n-1)$, so $frak(V)_n$ is countable. Therefore, $frak(V) = union.big_(n=0)^oo frak(V)_n$ is countable. 
    $qed$
]

#lemma[
    Suppose $Z, Z'$ are topological spaces and $f: Z' -> Z$ is a continuous open surjective mapping. If $Z'$ has countable topology, then $Z$ has countable topology.
    
]

#proof[
        Let $frak(U)$ be a countable basis for the topology of $Z'$ and $frak(V) = \{ f(U) : U in frak(U) \}$, which is a collection of open sets since $f$ is an open mapping. Since $f$ is surjective, $frak(V)$ is a basis of the topology of $Z$. Since $frak(U)$ is countable, $frak(V)$ is countable, hence $Z$ has countable topology.
     $qed$
]

#theorem(name: "Rado")[ 
    Let $X$ be a Riemann surface. Then $X$ is second countable, i.e. there exists a countable basis of the topology of $X$.
    
]

#proof[
        Let $(U, z)$ be a chart on $X$ and $K_0, K_1$ be two compact disks on $U$ with $K_0 inter K_1 = emptyset$. Set $Y := X without (K_0 union K_1)$. By Dirichlet boundary value problem, $exists u: overline(Y) -> RR$ such that $u$ is harmonic on $Y$ and $u|_(delta K_0) = 0$ and $u|_(delta K_1) = 1$. Let $omega = d u$, then $d''omega = d''(d' + d'')u = 0$, hence $omega$ is a non-constant holomorphic $1$-form on $Y$. Consider the universal covering $p: tilde(Y) -> Y$, then there exists a primitive $f in cal(O)(tilde(Y))$ such that $d f = p^* omega$. Since $omega$ is non-constant, $f$ is a non-constant holomorphic function $f: tilde(Y) -> CC$. 

        By Poincaré-Volterra lemma, $tilde(Y)$ has countable topology. By the previous lemma, since covering maps are open surjective continuous mappings, $Y$ has countable topology. Since $X$ is the union of an open chart and $Y$, $X$ has countable topology.
     $qed$
]

== Density of Holomorphic Functions

A Banach space is a complete normed vector space.
- A linear functional is continuous if and only if it is bounded, i.e. there exists $C > 0$ such that $|f(x)| <= C || x ||$ for every $x$ in the Banach space.
- (Banach theorem) A continuous surjective linear functional is an open mapping
- (Hahn-Banach theorem) Let $X$ be a Banach space, $Y$ be a linear subspace of $X$ and $f: Y -> CC$ be a continuous linear functional, then there exists a continuous linear functional $F: X -> CC$ such that $F|_Y = f$ and $|| F || = || f ||$.

#example[
    - $C_RR ([0, 1])$ is a Banach space with the supremum norm $|| f ||_oo = sup_(x in [0, 1]) |f(x)|$. 
    - $C_RR^k ([0, 1])$ is a Banach space with the norm
    $
    || f || := sum_(j=0)^k sup_(x in [0, 1]) |f^(j)(x)|, quad || f ||_k = sum_(j=0)^k || f^(j) ||_oo.
    $
    - $C_RR^oo ([0, 1])$ and $C_RR ((0, 1))$ are not Banach spaces with the above norms since they are not complete. 
]

=== Fréchet Spaces

#definition[
    A seminorm on a vector space $X$ is a function $p: X -> RR$ such that for every $x, y in X$ and $lambda in CC$, we have
    + $p(x + y) <= p(x) + p(y)$;
    + $p(lambda x) = |lambda| p(x)$.
    + $p(x) >= 0$.
]

Consider a countable family of seminormrs ${p_n}_{n in NN}$ such that they form a Fréchet space which is complete, on which Banach and Hahn-Banach theorems hold, as we can define a metric by
$
d(x, y) = sum_(n=1)^oo 2^(-n) dot (p_n (x - y))/(1 + p_n (x - y))
$
for every $x, y in X$. 

Let $X$ be a Riemann surface and $Y subset X$ be an open set. Since $Y$ has countable topology, we can find a countable family of compact subsets ${K_j}_{j in J}$ such that each $K_j$ is contained in a chart $(U_j, z_j)$ and
$
Y = union.big_(j in J) K_j^(circle.small).
$
For $j in J$ and $alpha in (alpha_1, alpha_2) in (NN union {0})^2$, define a seminorm $p_(j, alpha)$ on $cal(E)(Y)$ by
$
p_(j alpha)(f) = sup_(z in K_j) |D_j^alpha f(z)|
$
for every $f in cal(E)(Y)$. A neighborhood basis of $0$ is given by finite intersections of sets of the form
$
B(p_(j alpha), epsilon) = { f in cal(E)(Y) : p_(j alpha)(f) < epsilon })
$
for some $j in J$, $alpha in (NN union \{ 0 \})^2$ and $epsilon > 0$. Convergence $f_n -> f$ under this topology is equivalent to uniform convergence of $f_n$ and all its derivatives on each $K_j$. 

Analogously, we can define a Fréchet space structure on $cal(E)^(0, 1)(Y)$ by writing $omega in cal(E)^(0, 1)(Y)$ locally as $omega = f_j d overline(z_j)$ on $U_j$ for every $j in J$ and defining
$
p_(j alpha)(omega) := sup_(z in K_j) |D_j^alpha f_j(z)|
$
for every $omega in cal(E)^(0, 1)(Y)$, $j in J$ and $alpha in (NN union \{ 0 \})^2$.

#lemma(id: "lm:compact-support")[
    Suppose $Y$ is an open subset of a Riemann surface $X$. Then every continuous linear map $T: cal(E)(Y) -> CC$ has compact support, i.e. there exists a compact subset $K subset Y$ such that $T[f] = 0$ for every $f in cal(E)(Y)$ with $"supp" f subset.eq Y without K$.
]
#proof[
    Since $T$ is continuous, there exists $j_1, dots, j_m$,  $alpha_1, dots, alpha_m$ and $epsilon > 0$ such that $|T[f]| < 1$ for all $f in inter.big_(k=1)^m B(p_(j_k alpha_k), epsilon)$. Let $K = union.big_(k=1)^m K_(j_k)$, then $K$ is a compact subset of $Y$. For every $f in cal(E)(Y)$ with $"supp" f subset.eq Y without K$, we have $f|_K equiv 0$, hence $n f|_K equiv 0$ for every $n in NN$, so $
    p_(j_k alpha_k)(n f) = sup_(z in K_(j_k)) |D_(j_k)^(alpha_k) n f(z)| = 0
    $
    for every $k$ and $n$, hence $n f in inter.big_(k=1)^m B(p_(j_k alpha_k), epsilon)$ for every $n$, so $|T[n f]| < 1$ for every $n$, which implies that $T[f] = 0$.
    $qed$
]

#lemma(id: "lm:holomorphic-representation")[
    Suppose $Y$ is an open subset of a Riemann surface $X$ and $S: cal(E)^(0, 1)(X) -> CC$ is a continuous linear map such that $S[d''g] = 0$ for every $g in cal(E)(X)$ with $"supp" g subset.double Y$. Then there exists a holomorphic $1$-form $sigma in Omega(X)$ such that
    $
    S[omega] = integral.double_Y sigma and omega
    $
    for every $omega in cal(E)^(0, 1)(X)$ with $"supp" omega subset.double Y$.
]
#proof[
    Let $(U, z) subset Y$ be a chart. For $phi in cal(D)(U)$, define
    $
    tilde(phi) := cases(
        phi d overline(z) & "on" U ,
        0 & "on" X without U
    )
    $
    which is a smooth $(0, 1)$-form on $X$. Define a distribution on $U$ by
    $
    S_U: cal(D)(U) -> CC, quad phi |-> S[tilde(phi)].
    $
    By assumption, $S[d''g] = 0$ for every $g in cal(D)(U)$. Note that
    $
    (partial S_U)/(partial overline(z))[g] = S_U [(partial g)/(partial overline(z))] = S[(partial g)/(partial overline(z)) d overline(z)] = S[d''g] = 0
    $
    for all $g in cal(D)(U)$, hence $Delta S_U = 4d'd'' S_U = 0$, so by Weyl's lemma, exists $h in cal(O)(U)$ such that for all $g in cal(D)(U)$,
    $
    S[tilde(phi)] = S_U[phi] = integral.double_U h(z) phi(z) d z d overline(z) = integral.double_U (h(z) d z) and (phi(z) d overline(z)). 
    $
    Let $sigma_U = h(z) d z$ be the corresponding holomorphic 1-form on $U$ so that $S[omega] = integral.double_U sigma_U and omega$ for all $omega in cal(E)^(0, 1)(X)$ with $"supp" omega subset.double U$.

    On another chart $(U', z')$, we can similarly define a holomorphic $1$-form $sigma_(U')$ on $U'$. For $omega in cal(E)^(0, 1)(X)$ with $"supp" omega subset.double (U inter U')$, we have
    $
    integral.double_U sigma_U and omega = S[omega] = integral.double_(U inter U') sigma_(U') and omega,
    $
    for all $omega in cal(E)^(0, 1)(X)$ with $"supp" omega subset.double (U inter U')$, hence $sigma_U = sigma_(U')$ on $U inter U'$. Therefore, we can glue $sigma_U$ for all charts $(U, z) subset Y$ to get a holomorphic $1$-form $sigma in Omega(Y)$ such that $sigma|_U = sigma_U$, so
    $
    S[omega] = integral.double_Y sigma and omega
    $
    for every $omega in cal(E)^(0, 1)(X)$ with $"supp" omega$ relatively compact in some chart of $Y$. For an arbitrary $omega in cal(E)^(0, 1)(X)$ with $"supp" omega subset.double Y$, we can find a finite cover of $"supp" omega$ by charts $(U_j, z_j)$ and a partition of unity ${phi.alt_j}_{j=1}^n$ subordinate to the cover such that $phi.alt_j in cal(D)(U_j)$ for every $j$, hence
    $
    S[omega] = sum_(j=1)^n S[phi.alt_j omega] = sum_(j=1)^n integral.double_Y sigma and (phi.alt_j omega) = integral.double_Y sigma and omega.
    $
    $qed$
]

=== Runge Domain

#definition[
    For a subset $K subset X$, let $h_X(K)$ be the union of $K$ and all relatively compact connected components of $X without K$. 

    Let $X$ be a Riemann surface and $Y subset X$ be an open set. We say that $Y$ is a Runge domain if $h_X(Y) = Y$, i.e. no connected component of $X without Y$ is compact. 
]

#example[
    Consider
    $
    Y = { z in CC : 1 < |z| < 2 }. 
    $
    $Y$ is not Runge in $CC$ since $B_1 (0)$ is a connected component of $CC without Y$ that is compact. However, $Y$ is Runge in $CC^*$ since $B_1 (0)^*$ is not compact. 
]

#proposition(id: "prop:dense_restriction")[
    Let $X$ be a non-compact Riemann surface and $Y subset.double X$ be a Runge domain. If $Y subset Y' subset.double X$, then the image of the restriction map $beta: cal(O)(Y') -> cal(O)(Y)$ is dense in $cal(O)(Y)$. 
]
#proof[
    It suffices to show that for every continuous linear map $T: cal(E)(Y) -> CC$, $T|_(beta(cal(O)(Y'))) = 0$ implies $T|_(cal(O)(Y)) = 0$: to see this, suppose the $beta(cal(O)(Y'))$ is not dense in $cal(O)(Y)$, say $f_0 in cal(O)(Y) without overline(beta(cal(O)(Y')))$, then let
    $
    cal(E)_0 = overline(beta(cal(O)(Y'))) xor CC f_0 quad "and" quad T_0: cal(E)_0 -> CC, quad f + lambda f_0 |-> lambda
    $
    is a continuous linear map on $cal(E)_0$. By Hahn-Banach theorem, we can extend $T_0$ to a continuous linear map $T: cal(E)(Y) -> CC$. Then $T|_(beta(cal(O)(Y'))) = T_0|_(beta(cal(O)(Y'))) = 0$ but $T(f_0) = T_0(f_0) = 1$, contradiction.

    To prove the claim, suppose that $T|_(beta(cal(O)(Y'))) = 0$, i.e. $T[f] = 0$ for every $f in cal(O)(Y')$. By the general form of Dolbeault's lemma, for all $omega in cal(E)^(0, 1)(X)$, exists $f in cal(E)(Y')$ such that $omega|_Y' = d''f$, so we can define
    $
    S: cal(E)^(0, 1)(X) -> CC, quad omega |-> T[f|_Y].
    $
    $S$ is well-defined since if $d''f = omega = d''g$ on $Y'$, then $d''(f - g) = 0$ on $Y'$, so $f - g in cal(O)(Y')$, hence $T[f - g] = 0$. Consider the space
    $
    V = {(omega, f) in cal(E)^(0, 1)(X) times cal(E)(Y') : d''f = omega|_Y' },
    $
    which is a closed subspace since $d''$ is continuous, so $V$ is a Fréchet space. Note that the following diagram is commutative. 
    $
    #diagram(
        $
        V edge(->, pi_2) edge(->>, "d", pi_1) & cal(E)(Y') edge(->, beta) & cal(E)(Y) edge(->, "d", T, #left) \
        cal(E)^(0,1)(X) edge(->, "rr", S, #right) & & CC
        $
    )
    $
    Since $pi_1: V -> cal(E)^(0, 1)(X)$ is surjective, by Banach's theorem, $pi_1$ is an open mapping, and since $pi_2$, $beta$, $T$ are continuous, $S$ is also continuous. 

    By @lm:compact-support, there exist compact subsets $K subset Y$ and $L subset X$ such that
    + $T[f] = 0$ for every $f in cal(E)(Y)$ with $"supp" f subset.eq Y without K$;
    + $S[omega] = 0$ for every $omega in cal(E)^(0, 1)(X)$ with $"supp" omega subset.eq X without L$.
    We claim that $S[omega] = 0$ for every $omega in cal(E)^(0, 1)(X)$ with $"supp" omega subset.double X without h_X (K)$. If $f in cal(E)(X)$ with $"supp" f subset.double X without K$, then $S[d''f] = T[f|_Y] = 0$. By @lm:holomorphic-representation, there exists $sigma in Omega(X without K)$ such that
    $
    S[omega] = integral.double_(X without K) sigma and omega
    $
    for every $omega in cal(E)^(0, 1)(X)$ with $"supp" omega subset.double X without K$. By assumption, $sigma equiv 0$ on $(X without K) inter (X without L) = X without (K union L)$. Let $U$ be a connected component of $X without h_X(K)$, then $U inter (X without (K union L)) != emptyset$ otherwise $U$ is a non-compact connected component of $K union L$. Thus $sigma|_U = 0$ for every connected component $U$ of $X without h_X (K)$ by identity theorem, implying that $sigma|_(X without h_X (K)) equiv 0$, hence $S[omega] = 0$ for every $omega in cal(E)^(0, 1)(X)$ with $"supp" omega subset.double X without h_X (K)$.

    Finally, for all $f in cal(O)(Y)$, since $Y$ is a Runge domain and $K subset Y$, we have $h_X(K) subset h_X(Y) = Y$. Let $h_X(K) subset V subset Y$ with $V$ open in $Y$, and take $V subset overline(V) subset V' subset Y$, then by partition of unity, exists $phi in cal(E)(X)$ such that $phi|_V equiv 1$ and $"supp" phi subset.eq V'$. Set $g = phi f$. Note that $"supp" (f - g) subset.eq Y without V subset.eq Y without K$, hence $T[(f - g)|_Y] = 0$. Since $g$ is horomorphic on $V$, we have $"supp" d''g subset.double X without h_X (K)$, hence by our previous claim, 
    $
    T[f] = T[g|_Y] = S[d''g] = 0.
    $
]

== Runge Exhaustion

Let $X$ be a Riemann surface and $K subset X$ be nonempty. Recall that $h_X(K)$ is the union of $K$ and all relatively compact connected components of $X without K$. 

#proposition[
    If $K$ is closed, then $h_X(K)$ is closed. 
]
#proof[
    Let ${C_j}_(j in J)$ be the connected components of $X without K$, then each $C_j$ is open, so
    $
    X without h_X(K) = union.big_(j in J without J_0) C_j,
    $
    where $J_0 = { j in J : C_j "is relatively compact"}$, hence $X without h_X(K)$ is open, so $h_X(K)$ is closed.
    $qed$
]

#proposition[
    If $K$ is compact, then $h_X(K)$ is compact.
]
#proof[
    Let $U subset.double X$ be a relatively compact neighborhood of $K$. Let ${C_j}_(j in J)$ be the connected components of $X without K$, then each $C_j$ is open. 

    We claim that every $C_j$ meets $overline(U)$. Otherwise, exists some $j in J$ such that $C_j subset X without overline(U) subset X without U$. Since $X without U$ is closed, we have $overline(C_j) subset X without U subset X without K$. Since $C_j$ is a connected component of $X without K$, we have $overline(C_j) = C_j$, hence $C_j$ is closed. But $C_j$ is also open, contradicting the connectedness of $X$. 

    Since $partial U$ is compact and ${C_j}_(j in J)$ is a family of pairwise disjoint open subsets, there are at most finitely many $C_j$'s meeting $partial U$. Again, let
    $
    J_0 = { j in J : C_j "is relatively compact"},
    $
    and suppose $C_(j_1), dots, C_(j_m)$ are those that meet $partial U$, then by the previous claim all other components $C_j subset U$, so
    $
    h_X(K) subset U union (union.big_(k=1)^m C_(j_k)),
    $
    is relatively compact, and by the previous proposition, $h_X(K)$ is closed, hence $h_X(K)$ is compact.
    $qed$
]

#corollary(id: "compact-exhaustion")[
    Suppose $X$ is a non-compact Riemann surface, then there exists a sequence $(K_j)_(j=0)^oo$ of compact subsets of $X$ satisfying
    + $K_j$ is Runge in $X$ for every $j$;
    + $K_(j-1) subset K_j^circle.small$ for every $j >= 1$;
    + $union.big_(j=0)^oo K_j = X$.
]
#proof[
    Since $X$ has countable topology, exists a sequence of compact sets $(K_j ')_(j=0)^oo$ that covers $X$. Let $K_0 = K_0 '$. Choose a compact set $M_0$ such that $K_0 subset M_0^circle.small$ and set $K_1 = h(M_0)$. Choose a compact set $M_1$ such that $K_1 union K_1 ' subset M_1^circle.small$ and set $K_2 = h(M_1)$. Continuing this process, we can get a sequence of compact sets $(K_j)_(j=0)^oo$ such that $K_j$ is Runge in $X$ for every $j$, $K_(j-1) subset K_j^circle.small$ for every $j >= 1$ and $union.big_(j=0)^oo K_j = X$.
]

#lemma[
    For all compact $K subset X$, there exists a Runge domain $Y$ such that $K subset Y subset.double X$ and $Y$ has a regular boundary with respect to solving the Dirichlet problem. 
]
#proof[
    Choose a connected compact set $K_1 supset K$ and a compact set $K_2$ with $K_1 subset K_2^circle.small$. Let $K_2 ' = h_X (K_2)$. For each $x in partial K_2 '$, choose a chart $(U, z)$ around $x$ with $U inter K_1 = emptyset$ and $D_x := overline(B_(r_x)(x)) subset U$ for some $r_x > 0$. Since $partial K_2 '$ is compact, we can find a finite cover of $partial K_2 '$ by such disks $D_(x_1), dots, D_(x_m)$. Let
    $
    Y_1 = K_2 ' without (union.big_(k=1)^m D_(x_k)),
    $
    which is open and has regular boundary with respect to solving the Dirichlet problem. We claim that $Y_1$ is Runge in $X$. Let $C$ be a connected component of $X without Y_1$, then $C inter D_(x_k) != emptyset$ for some $k$ since $C inter partial K_2 ' != emptyset$, implying that $D_(x_k) subset Y_1$ since $D_(x_k)$ is connected, hence $D_(x_j) inter C_i' != emptyset$ for some connected component $C_i'$ of $X without K_2 '$, so $C_i' subset C$, hence $C$ is not compact since $C_i'$ is not compact. Therefore, $Y_1$ is Runge in $X$.

    Let $Y$ be the connected companennt of $Y_1$ containing $K_1$. Since $Y_1$ is open and $X$ is a manifold, $Y$ is open. Let $A := X without Y_1$ and ${A_k}$ are connected components of $A$, then each $A_k$ is closed and non-compact. If $overline(Y) inter A = emptyset$, then $overline(Y) subset X without A = Y_1$, so $Y = overline(Y)$ is closed and open, contradiction, thus $overline(Y) inter A != emptyset$. We claim tha each connected component $C$ of $X without Y$ meets $A$. Otherwise, $C subset Y_1$, i.e. exists connected component $Y'$ of $Y_1$ disjoint from $Y$ such that $C inter Y' != emptyset$. Since $C$ is a connected component of $X without Y$ and is closed and $Y' subset X without Y$ in connected, we have $Y' subset C$, so $overline(Y_1) subset C$ but $overline(Y') inter A != emptyset$, implying that $C inter A != emptyset$, contradiction. Therefore, each connected component of $X without Y$ meets $A$, hence is not compact since each connected component of $A$ is not compact, so $Y$ is connected hence a Runge domain. Since $Y_1$ has regular boundary with respect to solving the Dirichlet problem, so does $Y$ since $Y$ is a connected component of $Y_1$.
    $qed$
]

#theorem[
    Let $X$ be a non-compact Riemann surface, then there exists a sequence $Y_0 subset.double Y_1 subset.double dots subset.double X$  of relatively compact Runge domains such that $union.big_(j=0)^oo Y_j = X$ and each $Y_i$ has a regular boundary with respect to solving the Dirichlet problem. 
]
#proof[
    Let $(K_j)_(j=0)^oo$ be a sequence of compact subsets of $X$ satisfying the conditions in @compact-exhaustion. By the previous lemma, there exists a Runge domain $Y_0$ such that $K_0 subset Y_0 subset.double X$ and $Y_0$ has a regular boundary with respect to solving the Dirichlet problem. For $j >= 1$, suppose we already have $Y_0, dots, Y_(j-1)$, then we can find a Runge domain $Y_j$ such that $K_j union overline(Y_(j-1)) subset Y_j subset.double X$ and $Y_j$ has a regular boundary with respect to solving the Dirichlet problem. By construction, we have $Y_0 subset.double Y_1 subset.double dots subset.double X$, and we have
    $
    X = union.big_(j=0)^oo K_j subset.eq union.big_(j=0)^oo Y_j subset.eq X,
    $
    so $union.big_(j=0)^oo Y_j = X$.
    $qed$
]

== Runge Approximation

#theorem(id: "thm:runge_approximation", name: "Runge Approximation Theorem")[
    Let $X$ be a non-compact Riemann surface and $Y subset X$ be a Runge domain. Then for all holomorphic function $f in cal(O)(Y)$ and every compact subset $K subset Y$, there exists a sequence of holomorphic functions ${f_j}$ on $X$ such that $f_j -> f$ uniformly on $K$.
]
#proof[
    By replacing $f$ by $f|_V$ with $K subset V subset.double X$, we may assume that $Y subset.double X$. Let $Y = Y_0 subset.double Y_1 subset.double dots subset.double X$ be a special exhaustion of $X$ by Runge domains. By @prop:dense_restriction, exists $f_1 in cal(O)(Y_1)$ such that $||f_1 - f||_K < epsilon/2$. For $j >= 2$, by repeatedly applying @prop:dense_restriction, we can find $f_j in cal(O)(Y_j)$ such that $||f_j - f_(j-1)||_K < epsilon/2^j$. For every $n in NN$, the sequence $(f_j)_(j>n)$ converges uniformly on $Y_n$, hence converges to some holomorphic $g_n in cal(O)(Y_n)$. Note that $g_(n+1)|_(Y_n) = g_n$ for every $n$, so we can glue $g_n$ to get a holomorphic function $g in cal(O)(X)$ such that $g|_(Y_n) = g_n$ for every $n$, hence $f_j -> g$ uniformly on $K$. Since $||g - f||_K <= ||g - f_j||_K + ||f_j - f||_K < epsilon/2 + epsilon/2 = epsilon$, we conclude that every holomorphic function on $Y$ can be approximated uniformly on compact subsets by holomorphic functions on $X$.
]

#theorem(name: "General form (II) for Dolbeaut's lemma")[
    Let $X$ be a non-compact Riemann surface. For every $omega in cal(E)^(0, 1)(X)$, there exists $f in cal(E)(X)$ such that $d''f = omega$.
]
#proof[
    Pick $Y_0$ from @thm:general_dolbeault_i, such that $omega$ has local primitive on $Y_0$ and $Y_0 subset.double X$. Let $Y_0 subset.double Y_1 subset.double dots subset.double X$ be a special exhaustion of $X$ by Runge domains. We will construct functions $f_n in cal(E)(Y_n)$ such that $d''f_n = omega|_(Y_n)$ and $||f_(n+1) - f_n||_(overline(Y_(n-1))) <= 2^(-n)$. 

    Begin by choosing $f_0 in cal(E)(Y_0)$ such that $d''f_0 = omega|_(Y_0)$. Suppose that $f_0, dots, f_n$ have been constructed. By @thm:general_dolbeault_i, exists $g in cal(E)(Y_(n+1))$ such that $d''g = omega|_(Y_(n+1))$. On $Y_n$, $d''g = d''f_n = omega|_(Y_(n+1))$, $g - f_n in cal(O)(Y_n)$, so by @thm:runge_approximation, exists $h in cal(O)(Y_(n+1))$ such that $||h - (g - f_n)||_(overline(Y_(n-1))) < 2^(-n)$. Set $f_(n+1) = g - h in cal(E)(Y_(n+1))$, then $d''f_(n+1) = d''g = omega|_(Y_(n+1))$ and $||f_(n+1) - f_n||_(overline(Y_(n-1))) = ||h - (g - f_n)||_(overline(Y_(n-1))) < 2^(-n)$. Let $f = lim_(n -> oo) f_n$. Since
    $
    f = f_n + sum_(k=n)^oo (f_(k+1) - f_k),
    $
    $f in cal(E)(Y_n)$ for every $n$, so $f in cal(E)(X)$. Also, 
    $
    d''f = d''f_n + sum_(k=n)^oo d''(f_(k+1) - f_k) = omega|_(Y_n) + sum_(k=n)^oo (omega|_(Y_(k+1)) - omega|_(Y_k)) = omega|_(Y_n) = omega
    $
    on $Y_n$ for every $n$, hence $d''f = omega$ on $X$.
    $qed$
]

#corollary[
    Suppose $X$ is a non-compact Riemann surface, then
    $
    H^1(X, cal(O)) = 0.
    $
]
#proof[
    By the general form of Dolbeault's lemma, for every $cal(E)^(0, 1)(X) = d''(cal(E)(X))$, so $H^1(X, cal(O)) = cal(E)^(0, 1)(X) slash d''cal(E)(X) = 0$.
    $qed$
]

#lemma[
    Every divisor $D$ on a non-compact Riemann surface $X$ has a weak solution. 
]
#proof[
    Let $K_0 subset K_1 subset dots$ be a sequence of compact subsets such that
    + $K_j$ is Runge in $X$ for every $j$;
    + $K_(j-1) subset K_j^circle.small$ for every $j$;
    + $union.big_(j=0)^oo K_j = X$.

    Let $a_0 in X without K_(j_0)$. We claim that there exists a weak solution $f$ of $a_0$ with $f|_(K_(j_0)) equiv 1$. Since $K_(j_0)$ is Runge, $a_0 in U$ for some connected component of $X without K_(j_0)$ and $U$ is not relatively compact in $X$, i.e. $U subset.not K_(j_0 + 1)$. Pick $a_1 in U without K_(j_0 + 1)$ and let $c_0$ be a curve in $U$ from $a_1$ to $a_0$. By @lm:weak-solution-of-boundary, there exists a weak solution $f_0$ of $partial c_0 = a_1 - a_0$ with $f_0|_(X without U) equiv 1$. Similarly, for $a_l in X without K_(j_0 + l)$ and $c_l$ a curve in $X without K_(j_0 + l)$ from $a_(l+1)$ to $a_l$, exists a weak solution $f_l$ of $partial c_l = a_(l+1) - a_l$ with $f_l|_(K_(j_0 + l)) equiv 1$. Let $f = product_(l=0)^oo f_l$. For every $x in X$, $x in K_(j_0 + n)$ for some $n$, so $f|_(K_(j_0 + n)) = product_(l=0)^n f_l$ is well-defined, hence $f$ is a well-defined weak solution of $a_0$ with $f|_(K_(j_0)) equiv 1$.

    Given an arbitrary divisor $D in "Div"(X)$, for $j in N$, define
    $
    D_j (x) = cases(
        D(x) & "if" x in K_j without K_(j-1) ,
        0 & "if" x in.not K_j without K_(j-1)
    ).
    $
    Since each $K_j$ is compact, the divisor $D_j$ is a finite sum, hence by the previous claim, there exists a weak solution $g_j$ of $D_j$ with $g_j|_(K_(j-1)) equiv 1$. Since $D(x) = sum_j D_j(x)$, the function $g = product_(j=0)^oo g_j$ is a well-defined weak solution of $D$. 
]

#theorem(name: "Weierstrass Product Theorem")[
    Let $X$ be a non-compact Riemann surface, then for any divisor $D in "Div"(X)$, there exists a non-constant meromorphic function $f in cal(M)^* (X)$ such that $(f) = D$. 
]
#proof[
    Fix $x in X$, then there exists a relatively compact neighborhood $U_x$ of $x$ and a chart $(U_x, z)$ isomorphic to the unit disk, then $D|_(U_x)$ is finite, say $D|_(U_x) = sum_(i=1)^n r_i a_i$, then we can find a local solution $f_x(z) := product_(i=1)^n (z - a_i)^(r_i) in cal(M)^* (U_x)$ such that $(f_x) = D|_(U_x)$. Running through all $x in X$, there exists an open covering $frak(U) = (U_i)_(i in I)$ of $X$ and a family of local solutions $(f_i)_(i in I)$ such that $f_i in cal(M)^* (U_i)$ and $(f_i) = D|_(U_i)$ for every $i$. On the intersections, we have
    $
    (f_i)|_(U_i inter U_j) = D|_(U_i inter U_j) = (f_j)|_(U_i inter U_j) => (f_i)/(f_j) in cal(O)^* (U_i inter U_j).
    $
    By the previous lemma, there exists a global weak solution $psi$ of $D$. Write $psi = psi_i f_i$ on $U_i$, so that $psi_i in cal(E)(U_i)$ has no zeros. Since each $U_i$ is simply connected, there exists a logarithm $phi_i = log psi_i$ on $U_i$. On the intersections, we have
    $
    psi = f_j e^(phi_j) = f_i e^(phi_i) => e^(phi_j - phi_i) = (f_i)/(f_j) in cal(O)^* (U_i inter U_j),
    $
    so $phi_j - phi_i in cal(O)(U_i inter U_j)$. Define $phi_(i j) = phi_j - phi_i$, then $(phi_(i j)) in Z^1(frak(U), cal(O))$. Since $H^1(X, cal(O)) = 0$, we have $(phi_(i j)) in B^1(frak(U), cal(O))$, so exists a family of holomorphic functions $(g_i)_(i in I)$ such that $phi_j - phi_i = g_j - g_i$ on $U_i inter U_j$. Note that
    $
    e^(g_j - g_i) = e^(phi_j - phi_i) = (f_i)/(f_j) => f_i e^(g_i) = f_j e^(g_j)
    $
    on $U_i inter U_j$, so we can glue $f_i e^(g_i)$ to get a global meromorphic function $f in cal(M)^* (X)$ such that $f|_(U_i) = f_i e^(g_i)$ for every $i$, hence $(f) = D$.
]

#corollary(id: "cl:non-vanishing-1-form")[
    On every non-compact Riemann surface, there exists a holomorphic 1-form $omega in Omega(X)$ without zeros.
]
#proof[
    Let $g in cal(M)(X)$ be a non-constant meromorphic function, and set $D = -(d g)$, then by the Weierstrass product theorem, there exists a non-constant meromorphic function $f in cal(M)^* (X)$ such that $(f) = D$, then $omega := f thin d g$ is a holomorphic 1-form without zeros since $(omega) = (f) + (d g) = D - D = 0$.
]

#theorem[
    Let $X$ be a non-compact Riemann surface and $(a_j)_(j in NN)$ is a sequence of discrete points, then given any sequence of complex numbers $(c_j)_(j in NN)$, there exists a holomorphic function $f in cal(O)(X)$ such that $f(a_j) = c_j$ for every $j$.
]
#proof[
    Exists a holomorphic function $h in cal(O)(X)$ such that $(h) = sum_(j in NN) a_j$. Let $U_j = X without union_(l != j) {a_l}$, then $frak(U) := (U_j)_(j in NN)$ is an open cover of $X$. Let $g_j = (c_j)/h in cal(M)(U_j)$, then on the intersections $U_j inter U_k$, we have
    $
    g_j - g_k = (c_j - c_k)/h in cal(O)(U_j inter U_k),
    $
    so $(g_j - g_k) in Z^1(frak(U), cal(O))$. Since $H^1(X, cal(O)) = 0$, we have $(g_j - g_k) in B^1(frak(U), cal(O))$, so exists a global meromorphic function $g in cal(M)(X)$ such that $g|_(U_j) - g_j in cal(O)(U_j)$ for every $j$. Let $f = g h$, then on $U_j$, 
    $
    f = g h = g_j h + (g - g_j) h = c_j + (g - g_j) h,
    $
    so $f(a_j) = c_j$ for every $j$.
]

Recall that on a simply connected Riemann surface, 
$
"Rh"_(cal(O))^1 (X) := Omega(X) slash d cal(O)(X) = 0
$
since $H^1(X, CC) = 0$. 

#lemma[
    Suppose $X$ is a Riemann surface with $"Rh"_(cal(O))^1 (X) = 0$, then
    + for every holomorphic function $f in cal(O)^* (X)$, there exists $g in cal(O)(X)$ such that $f = e^g$;
    + every harmonic function $u: X -> RR$ is the real part of some holomorphic function $f in cal(O)(X)$.
]
#proof[
    + Note that $(d f)/f in Omega(X)$, so since $"Rh"_(cal(O))^1 (X) = 0$, exists $g_1 in cal(O)(X)$ such that $d g_1 = (d f)/f$, hence
        $
        d(f e^(-g_1)) = d f thin e^(-g_1) + f thin (-e^(-g_1) d g_1) = 0 => f thin e^(-g_1) equiv c in CC^*
        $
        set $g = g_1 + log c$ to get $f = e^g$.
    + Exists $omega in Omega(X)$ such that $"Re" omega = d u$. Since $Omega(X) = d cal(O)(X)$, exists $f in cal(O)(X)$ such that $d f = omega$, so $"Re" d f = "Re" omega = d u$, hence $u - "Re" f$ is a constant, so $u$ is the real part of the holomorphic function $f + i c$ for some $c in RR$.
]

#theorem(id: "thm:simple-riemann-mapping")[
    Suppose $X$ is a non-compact Riemann surface and $Y subset.double X$ is an open set, such that $"Rh"_(cal(O))^1 (Y) = 0$ and $Y$ has regular boundary. Then there exists a biholomorphic mapping from $Y$ to the unit disk. 
]
#proof[
    For $a in Y$, exists $g in cal(O)(X)$ such that $(g) = a$. Exists $u in C_(RR)(overline(Y))$ such that $u|_Y$ is harmonic and $u|_(partial Y) = log |g|$. By the previous lemma, exists $h in cal(O)(Y)$ such that $u = "Re" h$. Set $f := e^(-h) g in cal(O)(Y)$, then
    $
    |f| = |e^(-h + log g)| = e^(-u + log |g|). 
    $
    On $partial Y$, $e^(-u + log |g|) = 1$, so $|f|$ can be continued to a continuous function $phi$ on $overline(Y)$. By maximum principle, $|f| < 1$ on $Y$, so $f(Y) subset DD$. We now show that the mapping is proper. It suffices to show that for every $r < 1$, the preimage $Y_r$ of the disk $overline(B_R(0))$ is compact in $Y$. But
    $
    f^(-1) (overline(B_R(0))) = { y in Y : |f(y)| <= r } = { y in overline(Y) : phi(y) <= r }
    $
    is closed in $overline(Y)$, hence compact. Therefore, $f$ is a proper holomorphic mapping from $Y$ to $DD$. Since the value zero is taken exactly once by $f$ at $a$, $f$ is a biholomorphism from $Y$ to $DD$.
    $qed$
]

== Riemann Mapping Theorem

#theorem(name: "Riemann Mapping Theorem")[
    Let $X$ be a Riemann surface with $"Rh"_(cal(O))^1 (X) = 0$, then $X$ is biholomorphic to either $PP^1$, $CC$ or $DD$.
]
#proof[
    If $X$ is compact, then every holomorphic function on $X$ is constant, so $"Rh"_(cal(O))^1 (X) = Omega(X) slash d cal(O)(X) = Omega(X)$, so $Omega(X) = 0$. Since $dim Omega(X) = g(X)$, we have $g(X) = 0$, so $X$ is biholomorphic to $PP^1$. 

    Suppose $X$ is non-compact. Let $Y_0 subset.double Y_1 subset.double Y_2 subset.double dots.c$ be a special exhaustion of $X$ by Runge domains. We claim that $"Rh"_(cal(O))^1 (Y_i) = 0$ for each $i$. By @cl:non-vanishing-1-form, there exists a holomorphic 1-form $omega_0 in Omega(X)$ without zeros. Let $omega in Omega(Y_i)$ be an arbitrary holomorphic 1-form, then $omega = h omega_0$ for some meromorphic function $h$ on $Y_i$, but since $(h) = (omega) - (omega_0) >= 0$, $h$ is holomorphic. Let $alpha$ be a closed curve in $Y_i$, and let $K subset Y_i$ be some compact subset containing $alpha$. By Runge approximation, exists ${h_n} subset cal(O)(X)$ such that $h_n -> h$ uniformly on $K$, so
    $
    integral_alpha h_n omega_0 -> integral_alpha h omega_0 = integral_alpha omega,
    $
    but $integral_alpha h_n omega_0 = 0$ since $h_n omega_0$ is a holomorphic 1-form on $X$ and $"Rh"_(cal(O))^1 (X) = 0$, so $integral_alpha omega = 0$. Since $alpha$ is arbitrary, we have $omega$ has primitive on $Y_i$, so $"Rh"_(cal(O))^1 (Y_i) = 0$.

    By @thm:simple-riemann-mapping, for each $i$, there exists a biholomorphic mapping $g_i: Y_i -> DD$. Choose a point $a in Y_0$ and a chart $(U, z)$ around $a$ with $U subset Y_0$ and $z(a) = 0$. By some linear fractional transformations, exists some $f_i$ mapping $Y_i$ to some disk centered at $0$ with radius $r_i$ in $CC$. We claim that $r_n <= r_(n+1)$ for every $n$. Consider the mapping $h := f_(n+1) compose f_n^(-1)$, which sends $B_(r_n)$ to $B_(r_(n+1))$ and satisfies $h(0) = 0$ and $h'(0) = 1$. By Cauchy's integral formula, for $alpha = partial overline(B_(r_n-epsilon)(0))$ for $epsilon$ small, we have
    $
    h'(0) = 1/(2 pi i) integral.cont_alpha (h(z))/(z^2) d z,
    $
    so
    $
    |h'(0)| <= 1/(2 pi) integral.cont_alpha (|h(z)|)/(|z|^2) |d z| <= 1/(2 pi) (r_(n+1))/(r_n - epsilon)^2 2 pi (r_n - epsilon) = r_(n+1)/(r_n - epsilon),
    $
    hence $r_n <= r_(n+1)$ since $epsilon$ is arbitrary. Define $R = lim_(n -> oo) r_n in (0, oo]$. We claim that $X$ is biholomorphic to $B_R(0)$. 

    The mapping $z |-> f_0^(-1)(r_0 z)$ maps $D$ to $Y_0$ biholomorphically. Set
    $
    g_n(z) := 1/(r_0) f_n (f_0^(-1)(r_0 z)),
    $
    then $g_n: DD -> CC$ is an injective holomorphic mapping with $g_n(0) = 0$ and $g_n'(0) = 1$. By @thm:injective-holomorphic-compact, exists a subsequence ${g_(n_k^0)}$ of ${g_n}$ that converges uniformly on compact subsets, then ${f_(n_k^0)}$ also converges uniformly on compact subsets. Similarly, we can find a subsequence ${f_(n_k^1)}$ of ${f_(n_k^0)}$ that converges uniformly on compact subsets, and so on. By diagonalization, pick the subsequence ${f_(n_k)} = {f_(n_k^k)}$, then for every $m$, the sequence ${f_(n_k)}_(k>=m)$ converges uniformly on compact subsets of $Y_m$. Let $f = lim_(k -> oo) f_(n_k)$, then $f$ is an injective holomorphic mapping from $X$ to $B_R(0)$ such that $f(0) = 0$ and $f'(0) = 1$. We claim that $f$ is surjective. If not, then we have $"Rh"_(cal(O))^1 (X) = "Rh"_(cal(O))^1 (f(X)) = 0$. By @lm:shrink-holomorphic, exists some $r < R$ and holomorphic function $g: f(X) -> B_r(0)$ such that $g(0) = 0$ and $g'(0) = 1$. Choose $n$ large enough such that $r_n > r$ and set $h = g compose f compose f_n^(-1): B_(r_n)(0) -> B_r(0)$, then $h(0) = 0$ and $h'(0) = 1$, contradicting the Schwarz lemma since $r_n > r$. Therefore, $f$ is a biholomorphic mapping from $X$ to $B_R(0)$, so $X$ is biholomorphic to $B_R(0)$. If $R = oo$, then $X$ is biholomorphic to $CC$, otherwise, $X$ is biholomorphic to $DD$.
    $qed$
]

// --------------------------------

#theorem(id: "thm:injective-holomorphic-compact")[
    The set of all injective holomorphic functions from $DD$ to $CC$ with $f(0) = 0$ and $f'(0) = 1$ is compact in $cal(O)(DD)$.
]

#lemma(id: "lm:shrink-holomorphic")[
    If $0 in Y subset.neq B_R(0)$ with $0 < R <= oo$ and $"Rh"_(cal(O))^1 (Y) = 0$, then there exists some $r < R$ and holomorphic function $f: Y -> B_r(0)$ such that $f(0) = 0$ and $f'(0) = 1$.
]