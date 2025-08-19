#set par(leading: 1em, justify: true, first-line-indent: 1em)
#set page(numbering: "1")
#set text(font: ("New Computer Modern", "YuMincho"), lang: "ja")
#let cmt(it) = text(font: ("New Computer Modern", "YuMincho"), lang: "ja", box(it))
#show emph: it => $underline(#cmt(it.body))$
#show strong: it => {
	show math.equation: math.bold
	text(font: ("New Computer Modern", "YuGothic"), it)
}

#set heading(numbering: "1.")
#show heading: it => {
	set block(spacing: auto)
	strong(it)
}

#set footnote(numbering: it => $*$ + str(it))
#set footnote.entry(indent: 0em)

#show figure.caption.where(kind: image): it => {
  h(1cm)
  box(width: 1fr, align(left, {
    it.supplement
    context it.counter.display(it.numbering)
    h(1em)
    it.body
    v(1em)
  }))
  h(1cm)
}

#show ref: set text(red)
#set ref(supplement: none)

#show link: set text(green)

#import "@preview/physica:0.9.5": *

#let sp = sym.space

#show outline.entry.where(level: 1): it => [
  #v(1em)
  #strong(it)
]

#set outline.entry(fill: repeat($dot$))

#outline(title: [目次], indent: 1em)

#pagebreak()

= 電磁気学

== 鏡像法

#h(1em)曲面 $diff V$ を境界に持つ領域 $V$ におけるポアソン方程式 $
  laplace phi.alt (bold(x)) = - (rho (bold(x)))/epsilon_0
$ を、境界条件 $evaluated(phi.alt)_(diff V) = 0$ のもとで解くことを考える。境界条件の代わりに適切な鏡像電荷密度を置き、全空間でポアソン方程式を解くことで、$V$ において等価な解が得られることが知られている。以下に具体例を示す。

- $V = {(x , y , z) mid(|) x > 0}$ の場合

  鏡像電荷密度を $rho' (x , y , z) := - rho (- x , y , z)$ とすることで、$evaluated(phi.alt)_(x = 0) = 0$ が実現される。

- $V = {(r , theta , phi) mid(|) r > a}$ の場合

  鏡像電荷密度を $rho' (r , theta , phi) := - a/r rho (a^2/r , theta , phi)$ とすることで、$evaluated(phi.alt)_(r = a) = 0$ が実現される（アポロニウスの円を考えれば良い）。

\

== 電磁場のエネルギー（1） <電磁場のエネルギー1>

- 電磁場のエネルギー

  $bold(D) = epsilon bold(E)$, $bold(H) = 1/mu bold(B)$ が成り立つ場合を考える。マクスウェル方程式より、$
    div (bold(E) times bold(H)) & = (curl bold(E)) dot bold(H) - bold(E) dot (curl bold(H)) \
    & = - pdv(bold(B), t) dot bold(H) - bold(E) dot (pdv(bold(D), t) + bold(j)) \
    & = - pdv(, t)(1/2 bold(E) dot bold(D) + 1/2 bold(H) dot bold(B)) - bold(E) dot bold(j)
  $ $
    therefore sp pdv(, t)(1/2 bold(E) dot bold(D) + 1/2 bold(H) dot bold(B)) + div (bold(E) times bold(H)) + bold(E) dot bold(j) = 0
  $ が成り立つ。第3項は電磁場が物質にする仕事を表しているから、エネルギー保存則より、第1項と第2項は電磁場のエネルギー密度の増加を表す。よって、電磁場のエネルギー密度は $1/2 bold(E) dot bold(D) + 1/2 bold(H) dot bold(B)$ で与えられ、電磁場のエネルギーの流れはポインティング・ベクトル $bold(E) times bold(H)$ で与えられる。

  真空中では $bold(D) = epsilon_0 bold(E)$, $bold(H) = 1/mu_0 bold(B)$ が成り立つから、電磁場のエネルギー密度は $epsilon_0/2 abs(bold(E))^2 + 1/(2 mu_0) abs(bold(B))^2$, ポインティング・ベクトルは $1/mu_0 bold(E) times bold(B)$ となる。

- 黒体輻射

  @電磁場のエネルギー2 に記す。

\
参考文献：

- 砂川重信『理論電磁気学』

#pagebreak()

= 量子力学

== 1重項状態

#h(1em)スピン量子数が $s$ の状態には $m = - s , - s + 1 , dots.c , s$ の $2 s + 1$ 個があるため、$2 s + 1$ 重項状態という。2つの電子からなる系のスピン状態（@角運動量の合成）は3重項状態 $
  ket(1 "," 1) = ket(arrow.t) times.circle ket(arrow.t)
$ $
  ket(1 "," 0) = 1/sqrt(2) (ket(arrow.b) times.circle ket(arrow.t) + ket(arrow.t) times.circle ket(arrow.b))
$ $
  ket(1 "," - 1) = ket(arrow.b) times.circle ket(arrow.b)
$ と1重項状態 $
  ket(0 "," 0) = 1/sqrt(2) (ket(arrow.t) times.circle ket(arrow.b) - ket(arrow.b) times.circle ket(arrow.t))
$ から成る。パウリの排他原理により、同じ軌道にある2つの電子は必ず1重項状態になければならない。1重項状態は最大もつれ状態の1つであり、量子テレポーテーションなどのタスクで重要な役割を果たす。

\

== 角運動量の合成 <角運動量の合成>

#h(1em)角運動量とは、物理量の3つ組 $bold(J) = (J_x , J_y , J_z)$ であって、交換関係 $
  [J_j , J_k] = "i" hbar epsilon_(j k l) J_l
$ を満たすものである。$bold(J)^2 := J_x^2 + J_y^2 + J_z^2$, $J_plus.minus := J_x plus.minus "i" J_y$ とする。$[bold(J)^2 , J_z] = 0$ であるから、これらの同時固有状態を考えることができて、$
  bold(J)^2 ket(j "," m) = hbar^2 j (j + 1) ket(j "," m)
$ $
  J_z ket(j "," m) = hbar m ket(j "," m)
$ $
  j in {0 , 1/2 , 1 , dots.c} , quad m in {- j , - j + 1 , dots.c , j}
$ となる。$J_plus.minus$ の作用は $
  J_plus.minus ket(j "," m) = hbar sqrt(j (j + 1) - m (m plus.minus 1)) ket(j "," m plus.minus 1)
$ である#footnote[
  #h(1em)$[J_z , J_plus.minus] = plus.minus hbar J_plus.minus$ と $bold(J)^2 = J_- J_+ + J_z^2 + hbar J_z = J_+ J_- + J_z^2 - hbar J_z$ より得られる。
]。

// 角運動量によって区別できない状態を同一視すると、合成系のヒルベルト空間は ${ket(j^upright(A) "," m^upright(A)) times.circle ket(j^upright(B) "," m^upright(B))}_(j^upright(A) , m^upright(A), j^upright(B) , m^upright(A))$ を正規直交完全系に持つ。

// 係数 $
//   (bra(j^upright(A) "," m^upright(A)) times.circle bra(j^upright(B) "," m^upright(B))) ket(j^upright(A B) "," m^upright(A B) "," j^upright(A) "," j^upright(B))
// $ をクレプシュ--ゴルダン係数という。

2つの系 $upright(A)$, $upright(B)$ がそれぞれ角運動量 $bold(J)^upright(A)$, $bold(J)^upright(B)$ を持っているとし、それらの合成系を考える。角運動量の和 $bold(J)^upright(A B) := (J^upright(A)_x times.circle I^upright(B) + I^upright(A) times.circle J^upright(B)_x , J^upright(A)_y times.circle I^upright(B) + I^upright(A) times.circle J^upright(B)_y , J^upright(A)_z times.circle I^upright(B) + I^upright(A) times.circle J^upright(B)_z)$ は合成系の角運動量になっている。$(bold(J)^upright(A))^2$, $(bold(J)^upright(B))^2$, $(bold(J)^upright(A B))^2$, $J^upright(A B)_z$ は互いに交換するから、これらの同時固有状態 $ket(j^upright(A) "," j^upright(B) "," j^upright(A B) "," m^upright(A B))$ を考えることができる。この同時固有状態を、テンソル積状態 $ket(j^upright(A) "," m^upright(A)) times.circle ket(j^upright(B) "," m^upright(B))$ たちの線型結合として表したい（このときの展開係数をクレプシュ--ゴルダン係数という）。

以下では $j^upright(A)$, $j^upright(B)$ を固定して考え、量子数の表記から省略する。$m^upright(A B) = m^upright(A) + m^upright(B)$ が成り立つから、その最大値を考えることで、$j^upright(A B) <= j^upright(A) + j^upright(B)$ であることが分かる。特に、$
  ket(j^upright(A) + j^upright(B) "," j^upright(A) + j^upright(B)) = ket(j^upright(A)) times.circle ket(j^upright(B))
$ としてよい。この両辺に $J^upright(A B)_- = J^upright(A)_- times.circle I^upright(B) + I^upright(A) times.circle J^upright(B)_-$ を掛けていくことで、$ket(j^upright(A) + j^upright(B) "," j^upright(A) + j^upright(B) - 1) , ket(j^upright(A) + j^upright(B) "," j^upright(A) + j^upright(B) - 2) , dots.c , ket(j^upright(A) + j^upright(B) "," - j^upright(A) - j^upright(B))$ の表式が得られる。次に、$m^upright(A) + m^upright(B) = j^upright(A) + j^upright(B) - 1$ を満たす部分空間の次元は2であり、そのうち1つの状態は $ket(j^upright(A) + j^upright(B) "," j^upright(A) + j^upright(B) - 1)$ としてすでに得られているから、これと直交する状態を $ket(j^upright(A) + j^upright(B) - 1 "," j^upright(A) + j^upright(B) - 1)$ として良い。これに $J^upright(A B)_-$ を掛けていくことで、$j^upright(A B) = j^upright(A) + j^upright(B) - 1$ を満たす全ての状態が得られる。このようにして $j^upright(A B)$ を1つずつ下げていくことで、$j^upright(A B) = j^upright(A) + j^upright(B) , j^upright(A) + j^upright(B) - 1 , dots.c , abs(j^upright(A) - j^upright(B))$ までの全ての状態が得られる（$j^upright(A B) < abs(j^upright(A) - j^upright(B))$ にしようとしても独立な状態が残っていないはずである）。得られた状態の個数は $
  sum_(j^upright(A B) = abs(j^upright(A) - j^upright(B)))^(j^upright(A) + j^upright(B)) (2 j^upright(A B) + 1) = (2 j^upright(A) + 1) (2 j^upright(B) + 1)
$ となり、テンソル積状態の個数に一致する。以上の結果から、$
  j^upright(A B) in {abs(j^upright(A) - j^upright(B)) , abs(j^upright(A) - j^upright(B)) + 1 , j^upright(A) + j^upright(B)}
$ となることが分かる。

\
参考文献：

- J. J. Sakurai『現代の量子力学（上）』

\

== スピン--軌道相互作用 <スピン--軌道相互作用>

#h(1em)中心力ポテンシャル中の荷電粒子のハミルトニアンは $
  H_0 = 1/(2 m) bold(p)^2 + q phi.alt (r)
$ で与えられる。粒子がスピン角運動量 $bold(S)$ とそれによる磁気モーメント $
  bold(mu) = (g q)/(2 m) bold(S)
$ を持つ場合、相対論効果によりスピン--軌道相互作用項 $
  H_"LS" = xi (r) bold(L) dot bold(S) , quad xi (r) = ((g - 1) q)/(c^2 m^2 r) dv(phi.alt (r), r)
$ が付け加えられる#footnote[
  #h(1em)スピン--軌道相互作用は古典的には以下のようにして定性的に導出できる。電子が原子核の周りを公転している系を考えているとする。電子が静止する座標系では、原子核が電子の周りを公転することで磁場 $bold(B)_"eff" prop bold(L)$ を作る。これが電子の磁気モーメント $bold(mu) prop bold(S)$ と相互作用することでエネルギー $- bold(mu) dot bold(B)_"eff" prop bold(L) dot bold(S)$ が生じる。
]。ここで、$bold(L)$ は軌道角運動量である。全角運動量を $bold(J) = bold(L) + bold(S)$ とすると、$H_0$, $bold(L)^2$, $bold(S)^2$, $bold(J)^2$, $J_z$ は互いに交換するから、これらの同時固有状態を考えることができて、$
  H_0 ket(n "," l "," s "," j "," m_j) = E_(n , l) ket(n "," l "," s "," j "," m_j)
$ $
  bold(L)^2 ket(n "," l "," s "," j "," m_j) = hbar^2 l (l + 1) ket(n "," l "," s "," j "," m_j)
$ $
  bold(S)^2 ket(n "," l "," s "," j "," m_j) = hbar^2 s (s + 1) ket(n "," l "," s "," j "," m_j)
$ $
  bold(J)^2 ket(n "," l "," s "," j "," m_j) = hbar^2 j (j + 1) ket(n "," l "," s "," j "," m_j)
$ $
  J_z ket(n "," l "," s "," j "," m_j) = hbar m_j ket(n "," l "," s "," j "," m_j)
$ $
  n in {1 , 2 , dots.c} , quad l in {0 , 1 , dots.c , n - 1} , \
  j in {abs(l - s) , abs(l - s) + 1 , dots.c , l + s} , quad m_j in {- j , - j + 1 , dots.c , j}
$ となる（角運動量の合成（@角運動量の合成）を用いた）。$r$ が角運動量と交換することと、$bold(L) dot bold(S) = 1/2 (bold(J)^2 - bold(L)^2 - bold(S)^2)$ が成り立つことから、この基底は $H_0$ の固有空間内で $H_"LS"$ を対角化する。したがって、エネルギー固有値の1次補正は $
  E_(n , l , s , j)^((1)) & = bra(n "," l "," s "," j "," m_j) H_"LS" ket(n "," l "," s "," j "," m_j) \
  & = hbar^2/2 (j (j + 1) - l (l + 1) - s (s + 1)) bra(n "," l "," s "," j "," m_j) xi (r) ket(n "," l "," s "," j "," m_j) \
  & = hbar^2/2 (j (j + 1) - l (l + 1) - s (s + 1)) expval(xi (r))_(n , l)
$ によって計算できる。ここで、$r$ が角運動量と交換することから、$bra(n "," l "," s "," j "," m_j) xi (r) ket(n "," l "," s "," j "," m_j)$ は（$H_0$ と $r$ の非可換性によって）$n$, $l$ だけに依存するため、これを $expval(xi (r))_(n , l)$ と表した。

\
参考文献：

- J. J. Sakurai『現代の量子力学（下）』

\

== スレイター行列式

#h(1em)@第2量子化 に従った記法を用いる。フェルミオンの $n$ 粒子状態 $
  Psi & = 1/sqrt(n !) sum_(sigma in frak(S)_n) sgn (sigma) psi_(sigma (1)) times.circle psi_(sigma (2)) times.circle dots.c times.circle psi_(sigma (n))
$ を考える。波動函数表示では $
  Psi (x_1 , x_2 , dots.c , x_n) & = 1/sqrt(n !) sum_(sigma in frak(S)_n) sgn (sigma) psi_(sigma (1)) (x_1) psi_(sigma (2)) (x_2) dots.c psi_(sigma (n))(x_n) \
  & = 1/sqrt(n !) det mat(psi_1 (x_1), psi_2 (x_1), dots.c, psi_n (x_1); psi_1 (x_2), psi_2 (x_2), dots.c, psi_n (x_2); dots.v, dots.v, dots.down, dots.v; psi_1 (x_n), psi_2 (x_n), dots.c, psi_n (x_n);)
$ となる。このような状態をスレイター行列式状態という。$Psi$ が 0 でないための必要十分条件は ${psi_1 , psi_2 , dots.c , psi_n}$ が線型独立であることである。

${xi_j}_j$ を $cal(H)$ の正規直交完全系とすると、スレイター行列式状態の集合 $
  {b^dagger (xi_j_1) b^dagger (xi_j_2) dots.c b^dagger (xi_j_n) Omega_cal(H) mid(|) n in {0 , 1 , 2, dots.c} , sp j_1 < j_2 < dots.c < j_n}
$ は $cal(F)_upright(f) (cal(H))$ の正規直交完全系を成す。

\
参考文献：

- 田崎晴明『非相対論的量子力学における生成・消滅演算子の方法（いわゆる「第二量子化」）の手引き』https://www.gakushuin.ac.jp/~881791/pdf/2ndQNoteJ.pdf

\

== ゼーマン分裂

#h(1em)中心力ポテンシャル中の荷電粒子（電荷 $q$）のハミルトニアン $
  H = 1/(2 m) bold(p)^2 + q phi.alt(r)
$ において、ハミルトニアンと軌道角運動量 $bold(L)^2$, $L_z$ の同時固有状態を考えることができて、$
  H ket(n "," l "," m_l) = E_(n , l) ket(n "," l "," m_l)
$ $
  bold(L)^2 ket(n "," l "," m_l) = hbar^2 l (l + 1) ket(n "," l "," m_l)
$ $
  L_z ket(n "," l "," m_l) = hbar m_l ket(n "," l "," m_l)
$ $
  n in {1 , 2 , dots.c} , quad l in {0 , 1 , dots.c , n - 1} , quad m_l in {- l , - l + 1 , dots.c , l}
$ となる。ここに一様な磁束密度 $bold(B) = (0 , 0 , B)$ を加えたときのエネルギー準位の変化を考える。この磁束密度を与えるベクトルポテンシャルとして $bold(A) = (- B/2 y , B/2 x , 0)$ をとる。このとき、ハミルトニアンを $B$ の1次まで展開すると $
  H & = 1/(2 m) ((p_x + (q B)/2 y)^2 + (p_y - (q B)/2 x)^2 + p_z^2) + q phi.alt(r) \
  & tilde.eq 1/(2 m) bold(p)^2 + q phi.alt(r) - (q B)/(2 m) L_z
$ となる。エネルギー固有値の1次補正は $
  E_(n , l , m_l)^((1)) = bra(n "," l "," m_l) (- (q B)/(2 m) L_z) ket(n "," l "," m_l) = - (hbar q B)/(2 m) m_l
$ となる。これによりエネルギー固有値が $2 l + 1$ 個に分裂する。これを正常ゼーマン効果という。さらにスピン--軌道相互作用（@スピン--軌道相互作用）の効果を加えたものは異常ゼーマン効果という。

\
参考文献：

- J. J. Sakurai『現代の量子力学（下）』

\

== ゼロ点振動

#h(1em)量子力学において、位置の標準偏差 $Delta x$ と運動量の標準偏差 $Delta p$ の間には不確定性関係（@不確定性関係） $
  Delta x Delta p >= hbar/2
$ が成り立つ。運動エネルギーの期待値は $
  expval(1/(2 m) p^2) >= (expval(p^2) - expval(p)^2)/(2 m) = (Delta p)^2/(2 m) >= hbar^2/(8 m (Delta x)^2)
$ となるから、固体中の原子などで位置が有限の範囲に束縛されている場合には、運動エネルギーの期待値は必ず正の値を持つ。これにより、原子は基底状態においても運動エネルギーを持つことになる。これをゼロ点振動という。ヘリウムが常圧において絶対零度極限でも固体にならないのはゼロ点振動によるものであるとされる。

- 調和振動子の運動エネルギー #h(1fr)

  調和振動子（@調和振動子）の運動エネルギーの期待値は $
    bra(n) 1/(2 m) p^2 ket(n) = bra(n) 1/(2 m) (sqrt(2 hbar m omega)/(2 "i") (a - a^dagger))^2 ket(n) = - (hbar omega)/4 bra(n) (a - a^dagger)^2 ket(n) = (hbar omega)/2 (n + 1/2)
  $ となり、基底状態 $ket(0)$ においても正の値を持つ。

\

== 第2量子化 <第2量子化>

#h(1em)第2量子化とは、1粒子状態を表すヒルベルト空間を拡張したフォック空間を考えることで、多粒子状態を扱えるようにすることであり、場の量子論などで用いられる。

- 全フォック空間

  1粒子状態がヒルベルト空間 $cal(H)$ 上のベクトルで表されるような粒子を考える。$n$ 粒子状態は $n$ 重テンソル積空間 $cal(H)^(times.circle n)$ 上のベクトルである。全フォック空間はこれらの無限直和空間 $
    cal(F) (cal(H)) & := plus.circle.big_(n = 0)^oo cal(H)^(times.circle n) \
    & = CC plus.circle cal(H) plus.circle (cal(H) times.circle cal(H)) plus.circle (cal(H) times.circle cal(H) times.circle cal(H)) plus.circle dots.c
  $ として定義される。多粒子状態 $Psi in cal(F) (cal(H))$ は、その $n$ 粒子成分を順に並べた $
    Psi = Psi^((0)) plus.circle Psi^((1)) plus.circle Psi^((2)) plus.circle dots.c
  $ という表示を持つ。0粒子成分だけを持つ多粒子状態 $
    Omega_cal(H) := 1 plus.circle 0 plus.circle 0 plus.circle dots.c
  $ を真空状態という。1粒子状態に作用する演算子 $T : cal(H) -> cal(H)$ に対して、第2量子化演算子 $dif Gamma (T) : cal(F) (cal(H)) -> cal(F) (cal(H))$ が $
    dif Gamma (T) & := plus.circle.big_(n = 0)^oo (sum_(j = 1)^n I^(times.circle (j - 1)) times.circle T times.circle I^(times.circle (n - j))) \
    & = 0 plus.circle T plus.circle (T times.circle I + I times.circle T) plus.circle (T times.circle I times.circle I + I times.circle T times.circle I + I  times.circle I times.circle T) plus.circle dots.c
  $ によって定義される。恒等演算子 $I$ の第2量子化演算子 $N := dif Gamma (I)$ を個数演算子という。$N$ は多粒子状態の $n$ 粒子成分を $n$ 倍するような演算子になっている。// 第2量子化演算子は $[dif Gamma (S) , dif Gamma (T)] = dif Gamma ([S , T])$ を満たす。

  // 1粒子状態に作用する演算子 $T : cal(H) -> cal(H)$ に対して、2種類の第2量子化演算子 $
  //   dif Gamma (T) := plus.circle.big_(n = 0)^oo sum_(j = 1)^n I^(times.circle (j - 1)) times.circle T times.circle I^(times.circle (n - j))
  // $ $
  //   Gamma (T) := plus.circle.big_(n = 0)^oo T^(times.circle n)
  // $ が定義される#footnote[
  //   #h(1em)$dif Gamma$ は加法的、$Gamma$ は乗法的な第2量子化だと思うことができる。
  // ]。これらの間には $Gamma ("e"^("i" t T)) = "e"^("i" t dif Gamma (T))$ という関係がある。

- ボソン・フォック空間とフェルミオン・フォック空間

  物理的な多粒子状態は、ボソンの場合は粒子の入れ替えに関して対称であり、フェルミオンの場合は反対称である。このような粒子を扱うために、全フォック空間の制限として、ボソン・フォック空間とフェルミオン・フォック空間を考える。対称化演算子 $S_n : cal(H)^(times.circle n) -> cal(H)^(times.circle n)$ と反対称化演算子 $A_n : cal(H)^(times.circle n) -> cal(H)^(times.circle n)$ を $
    S_n (psi_1 times.circle psi_2 times.circle dots.c times.circle psi_n) = 1/(n!) sum_(sigma in frak(S)_n) psi_(sigma (1)) times.circle psi_(sigma (2)) times.circle dots.c times.circle psi_(sigma (n))
  $ $
    A_n (psi_1 times.circle psi_2 times.circle dots.c times.circle psi_n) = 1/(n!) sum_(sigma in frak(S)_n) sgn (sigma) psi_(sigma (1)) times.circle psi_(sigma (2)) times.circle dots.c times.circle psi_(sigma (n))
  $ によって定義する#footnote[
    #h(1em)直積状態以外に対しては線型性により定義を拡張する。これらの演算子は冪等性 $S_n^2 = S_n$, $A_n^2 = A_n$ を満たす（すなわち、射影演算子になっている）。
  ]。ボソン・フォック空間 $cal(F)_upright(b) (cal(H))$ とフェルミオン・フォック空間 $cal(F)_upright(f) (cal(H))$ は $
    cal(F)_upright(b) (cal(H)) := plus.circle.big_(n = 0)^oo S_n (cal(H)^(times.circle n))
  $ $
    cal(F)_upright(f) (cal(H)) := plus.circle.big_(n = 0)^oo A_n (cal(H)^(times.circle n))
  $ によって定義される。これらは全フォック空間の部分空間である。

- 生成・消滅演算子

  1粒子状態 $psi in cal(H)$ に対して、ボソン生成演算子 $a^dagger (psi) : cal(F)_upright(b) (cal(H)) -> cal(F)_upright(b) (cal(H))$ とフェルミオン生成演算子 $b^dagger (psi) : cal(F)_upright(f) (cal(H)) -> cal(F)_upright(f) (cal(H))$ を $
    a^dagger (psi) (Phi^((0)) plus.circle Phi^((1)) plus.circle Phi^((2)) plus.circle dots.c) = 0 plus.circle (sqrt(1) S_1 (psi times.circle Phi^((0)))) plus.circle (sqrt(2) S_2 (psi times.circle Phi^((1)))) plus.circle dots.c
  $ $
    b^dagger (psi) (Phi^((0)) plus.circle Phi^((1)) plus.circle Phi^((2)) plus.circle dots.c) = 0 plus.circle (sqrt(1) A_1 (psi times.circle Phi^((0)))) plus.circle (sqrt(2) A_2 (psi times.circle Phi^((1)))) plus.circle dots.c
  $ によって定義する。また、$a^dagger (psi)$ の共軛演算子 $a (psi)$ をボソン消滅演算子、$b^dagger (psi)$ の共軛演算子 $b (psi)$ をフェルミオン消滅演算子という。生成（消滅）演算子は指定された1粒子状態を持った粒子を1つ生成する（消滅させる）演算子である。特に、真空状態に対して $
    a (psi) Omega_cal(H) = b (psi) Omega_cal(H) = 0
  $ が成り立つ #footnote[
    #h(1em)これは真空状態の特徴付けになっている。すなわち、消滅演算子によって消される多粒子状態は真空状態 $Omega_cal(H)$ の定数倍に限られる。
  ]。ボソン生成・消滅演算子は正準交換関係 $
    [a (psi) , a^dagger (phi)] = braket(psi, phi) , quad [a (psi) , a (phi)] = [a^dagger (psi) , a^dagger (phi)] = 0
  $ を満たし、フェルミオン生成・消滅演算子は正準反交換関係 $
    {b (psi) , b^dagger (phi)} = braket(psi, phi) , quad {b (psi) , b (phi)} = {b^dagger (psi) , b^dagger (phi)} = 0
  $ を満たす。

  第2量子化演算子を生成・消滅演算子を用いて表すことができる。${xi_j}_j$ を $cal(H)$ の正規直交完全系とする。ボソン・フォック空間において、$
    dif Gamma (T) = sum_j a^dagger (T xi_j) a (xi_j) = sum_(j , k) a^dagger (xi_k) braket(xi_k, T xi_j)a (xi_j)
  $ が成り立つ#footnote[
    #h(1em)2番目の等号は $a^dagger (psi)$ が $psi$ に関して線型であることから成り立つ。
  ]。特に、個数演算子は $
    N = sum_j a^dagger (xi_j) a (xi_j)
  $ と表される。フェルミオン・フォック空間においては、$
    dif Gamma (T) = sum_j b^dagger (T xi_j) b (xi_j) = sum_(j , k) b^dagger (xi_k) braket(xi_k, T xi_j)b (xi_j)
  $ が成り立つ。特に、個数演算子は $
    N = sum_j b^dagger (xi_j) b (xi_j)
  $ と表される。これらの表示は、$dif Gamma (T)$ が1粒子状態 $xi_j$ を持つ粒子を消滅させて1粒子状態 $T xi_j$ を持つ粒子を生成することを表している。

  ボソン・フォック空間において、第2量子化演算子と生成・消滅演算子の交換関係は $
    [dif Gamma (T) , a^dagger (psi)] = a^dagger (T psi) , quad [dif Gamma (T) , a (psi)] = - a (T^dagger psi)
  $ となる。フェルミオン・フォック空間においては、$
    [dif Gamma (T) , b^dagger (psi)] = b^dagger (T psi) , quad [dif Gamma (T) , b (psi)] = - b (T^dagger psi)
  $ となる。

\
参考文献：

- 新井朝雄『フォック空間と量子場 上』

- 田崎晴明『非相対論的量子力学における生成・消滅演算子の方法（いわゆる「第二量子化」）の手引き』https://www.gakushuin.ac.jp/~881791/pdf/2ndQNoteJ.pdf

\

== 調和振動子 <調和振動子>

#h(1em)調和振動子は、ポテンシャルの極小点の周りでの粒子の振る舞いを説明する模型であり、そのハミルトニアンは $
  H = 1/(2 m) p^2 + (m omega^2)/2 x^2
$ で与えられる。正準交換関係 $[x , p] = "i" hbar$ を仮定する。消滅演算子 $a$ と生成演算子 $a^dagger$ を $
  a := 1/sqrt(2 hbar) (sqrt(m omega) x + "i"/sqrt(m omega) p) , quad a^dagger := 1/sqrt(2 hbar) (sqrt(m omega) x - "i"/sqrt(m omega) p)
$ によって定めると、$[a , a^dagger] = 1$ を満たし、ハミルトニアンは $
  H = hbar omega (a^dagger a + 1/2)
$ と表される。

$H$ の固有値を調べるために、個数演算子 $N := a^dagger a$ を考える。固有状態 $N ket(psi) = lambda ket(psi)$ に対して、$
  N a ket(psi) = (a N + [N , a]) ket(psi) = (a N - a) ket(psi) = (lambda - 1) a ket(psi)
$ が成り立つから、$a ket(psi) eq.not 0$ であれば、$lambda - 1$ は $N$ の固有値である。一方、$N$ は半正定値であり、固有値に下限が存在するから、ある非負整数 $n$ が存在して $a^(n + 1) ket(psi) = 0$ となる。このとき、$N a^n ket(psi) = 0$ となるから、$N ket(psi) = n ket(psi)$ である。したがって、$N$ の固有値は非負整数である。

逆に、任意の非負整数が $N$ の固有値であり、さらに縮退がないことを示す。状態 $ket(0)$ に対して $N ket(0) = 0$ となるための必要十分条件は $a ket(0) = 0$ であることである。これを波動函数についての微分方程式として解くことで、$braket(x, 0) prop "e"^(- m omega x^2 \/ (2 hbar))$ となることが示される。したがって、0は $N$ の固有値であり、縮退度は1である。非負整数 $n$ が $N$ の固有値であり、縮退度が1であると仮定し、その規格化された固有状態を $ket(n)$ とする。このとき、$
  N a^dagger ket(n) = (a^dagger N + [N , a^dagger]) ket(n) = (a^dagger N + a^dagger) ket(n) = (n + 1) a^dagger ket(n)
$ が成り立つ。$norm(a^dagger ket(n)) = sqrt(bra(n) a a^dagger ket(n)) = sqrt(bra(n) (N + 1) ket(n)) = sqrt(n + 1)$ より、$a^dagger ket(n) eq.not 0$ であるから、$n + 1$ は $N$ の固有値である。また、固有値 $n + 1$ の固有状態 $ket(n + 1)$ に対して、$N a ket(n + 1) = n a ket(n + 1)$ が成り立つから、$ket(n + 1) prop a^dagger a ket(n + 1) prop a^dagger ket(n)$ となる。したがって、$N$ の固有値 $n + 1$ の縮退度は1である。

以上により、$H$ の固有値は $
  E = hbar omega (n + 1/2) , quad n in {0 , 1 , 2, dots.c}
$ であり、縮退度は全て1である。

\

== 不確定性関係 <不確定性関係>

- ケナード--ロバートソンの不確定性関係

  古典論では、純粋状態において全ての物理量が確定した値を持つ。一方、量子論では、非可換な物理量が同時に確定した値を持つことはない。

  ヒルベルト空間 $cal(H)$ で表される量子系における物理量 $A$, $B$ を考える。これらは $cal(H)$ 上の自己共軛演算子である。状態 $rho$ は $cal(H)$ 上の密度演算子（$tr rho = 1$ を満たす半正定値演算子）である。状態 $rho$ における物理量 $A$ の測定値は、期待値 $tr (rho A)$ および標準偏差 $
    (Delta A)_rho := sqrt(tr (rho (A - tr (rho A))^2))
  $ を持った確率分布に従う。$tilde(A) := A - tr (rho A)$, $tilde(B) := B - tr (rho B)$ とすると、$
    (Delta A)_rho (Delta B)_rho & = sqrt(tr (rho tilde(A)^2)) sqrt(tr (rho tilde(B)^2)) >= abs(tr (rho tilde(A) tilde(B))) >= abs(Im tr (rho tilde(A) tilde(B))) \
    & = 1/2 abs(tr (rho [tilde(A) , tilde(B)])) = 1/2 abs(tr (rho [A , B]))
  $ が成り立つ#footnote[
    #h(1em)最初の不等号はヒルベルト--シュミット内積 $expval(X "," Y) := tr (X^dagger Y)$ に関するコーシー--シュワルツ不等式 $sqrt(expval(X "," X)) sqrt(expval(Y "," Y)) >= abs(expval(X "," Y))$ において $X = tilde(A) sqrt(rho)$, $Y = tilde(B) sqrt(rho)$ としたものである。
  ]。特に、位置と運動量に対して、$
    (Delta x)_rho (Delta p)_rho >= hbar/2
  $ が得られる。

- 同時測定における不確定性関係

  可換な物理量は誤差無しで同時測定することができる（同時対角化する基底を用いて測定すれば良い）。一方、非可換な物理量の同時測定には誤差が伴う。系 $upright(S)$ の可換とは限らない物理量 $A$, $B$ を考える。測定器 $upright(P)$ の物理量を $R_A$, $R_B$ とし、これらは可換であるとする。系と測定器をユニタリ演算子 $U$ で相互作用させた後の物理量 $U^dagger (I_upright(S) times.circle R_A) U$, $U^dagger (I_upright(S) times.circle R_B) U$ を測定する#footnote[
    #h(1em)ハイゼンベルク描像を用いている。
  ]。このときの測定誤差を表す演算子を $
    N_A := U^dagger (I_upright(S) times.circle R_A) U - A times.circle I_upright(P) , quad N_B := U^dagger (I_upright(S) times.circle R_B) U - B times.circle I_upright(P)
  $ によって定義する。物理量 $R_A$, $R_B$, 相互作用 $U$, 測定器の状態 $rho_upright(P)$ をうまく選ぶことで、不偏性条件 $
    tr_upright(P) ((I_upright(S) times.circle rho_upright(P)) N_A) = tr_upright(P) ((I_upright(S) times.circle rho_upright(P)) N_B) = 0
  $ を満たすようにする。この条件は、系の任意の状態に対して $U^dagger (I_upright(S) times.circle R_A) U$ と $U^dagger (I_upright(S) times.circle R_A) U$ の期待値が $A$ と $B$ の期待値に一致することを表す。このとき、$
    0 & = [U^dagger (I_upright(S) times.circle R_A) U , U^dagger (I_upright(S) times.circle R_B) U] \
    & = [A times.circle I_upright(P) , B times.circle I_upright(P)] + [A times.circle I_upright(P) , N_B] + [N_A , B times.circle I_upright(P)] + [N_A , N_B] \
  $ の両辺の期待値を取ると、$
    0 & = tr_upright(S P) ((rho_upright(S) times.circle rho_upright(P)) [A times.circle I_upright(P) , B times.circle I_upright(P)]) + tr_upright(S P) ((rho_upright(S) times.circle rho_upright(P)) [A times.circle I_upright(P) , N_B]) \
    & quad quad quad quad + tr_upright(S P) ((rho_upright(S) times.circle rho_upright(P)) [N_A , B times.circle I_upright(P)]) + tr_upright(S P) ((rho_upright(S) times.circle rho_upright(P)) [N_A , N_B]) \
    & = tr_upright(S) (rho_upright(S) [A , B]) + tr_upright(S) (rho_upright(S) [A , tr_upright(P) ((I_upright(S) times.circle rho_upright(P)) N_B)]) \
    & quad quad + tr_upright(S) (rho_upright(S) [tr_upright(P) ((I_upright(S) times.circle rho_upright(P)) N_A) , B]) + tr_upright(S P) ((rho_upright(S) times.circle rho_upright(P)) [N_A , N_B]) \
    & = tr_upright(S) (rho_upright(S) [A , B]) + tr_upright(S P) ((rho_upright(S) times.circle rho_upright(P)) [N_A , N_B])
  $ となる。これとケナード--ロバートソンの不確定性関係より、不等式 $
    (Delta N_A)_(rho_upright(S) times.circle rho_upright(P)) (Delta N_B)_(rho_upright(S) times.circle rho_upright(P)) >= 1/2 abs(tr_upright(S P) ((rho_upright(S) times.circle rho_upright(P)) [N_A , N_B])) = 1/2 abs(tr_upright(S) (rho_upright(S) [A , B]))
  $ が成り立つ。特に、位置と運動量の同時測定に関して、$
    (Delta N_A)_(rho_upright(S) times.circle rho_upright(P)) (Delta N_B)_(rho_upright(S) times.circle rho_upright(P)) >= hbar/2
  $ が得られる。

\
参考文献：

- 沙川貴大・上田正仁『量子測定と量子制御』

- 上田正仁『量子光学講義ノート』http://cat.phys.s.u-tokyo.ac.jp/lecture/QO_24/QO_24.html

\

== ランダウ準位

#h(1em)電磁場中の荷電粒子（電荷 $q$）のハミルトニアンは $
  H = 1/(2 m) (bold(p) - q bold(A))^2 + q phi.alt
$ で与えられる。一様な磁束密度 $bold(B) = (0 , 0 , B)$ を考える。この磁束密度を与えるベクトルポテンシャルとして $bold(A) = (0 , B x , 0)$ をとる。このとき、ハミルトニアンは $
  H = 1/(2 m) (p_x^2 + (p_y - q B x)^2 + p_z^2)
$ となる。$H$, $p_y$, $p_z$ は互いに交換するから、これらの同時固有状態 $ket(E "," k_y "," k_z)$ を考えることができて、$
  E ket(E "," k_y "," k_z) & = H ket(E "," k_y "," k_z) \
  & = 1/(2 m) (p_x^2 + (k_y - q B x)^2 + k_z^2) ket(E "," k_y "," k_z) \
  & = (1/(2 m) p_x^2 + m/2 ((q B)/m)^2 (x - k_y/(q B))^2 + k_z^2/(2 m)) ket(E "," k_y "," k_z)
$ となる。これは調和振動子のハミルトニアンであり、固有値は $
  E = (hbar q B)/m (n + 1/2) + k_z^2/(2 m) , quad n in {0 , 1 , 2, dots.c}
$ である。この結果はゲージ不変である（ベクトルポテンシャルの選び方によらない）。このように、磁場に垂直な方向の運動エネルギーは離散的な準位をとる。これをランダウ準位という。

ランダウ準位の半古典的な解釈は以下のとおりである。前期量子論では、調和振動子において1周期で位相が元に戻るためには断熱不変量 $E/omega$ が $hbar$ の整数倍になる必要があるとされた。これをサイクロトロン運動（振動数 $omega = (q B)/m$）に適用することで、ランダウ準位が得られる。

\

== 量子エンタングルメント

#h(1em)...

#pagebreak()

= 熱力学・統計力学

== イジング模型 <イジング模型>

#h(1em)イジング模型は $plus.minus 1$ の値をとる変数 $sigma$ が格子点上に配置された模型であり、そのハミルトニアンは $
  H = - J sum_expval(j "," k) sigma_j sigma_k - h sum_j sigma_j
$ で与えられる。第1項は最近接格子点の組 $expval(j "," k)$ について和を取ることを表す。$sigma$ はスピン、$h$ は磁場と解釈される。$J$ は最近接スピン間の相互作用を表すパラメータであり、$J > 0$ のとき強磁性相互作用、$J < 0$ のとき反強磁性相互作用があるという。

イジング模型を解くとは、上記のハミルトニアンに関して自由エネルギー $g (beta , h)$ を求めることをいう。次元 $d = 1$ の場合と、$d = 2$ で $h = 0$ である場合の厳密解が知られている。イジング模型は、$d > 1$ のとき有限温度で相転移を起こす。$d > 4$ では臨界指数が平均場近似（@平均場近似）によるものと一致する。$d -> oo$ では平均場近似が厳密に成り立つ。

\
参考文献：

- 高橋和孝・西森秀稔『相転移・臨界現象とくりこみ群』

\

== 1次相転移 <一次相転移>

#h(1em)熱力学的状態空間（エントロピーの自然な変数によって張られる空間）上の連続的な経路の途中で、完全な熱力学函数（エントロピー $S (U , bold(X))$, 内部エネルギー $U (S , bold(X))$、あるいはそれらをいくつかの変数についてルジャンドル変換したもの）のいずれかが解析的でなくなるとき、相転移があるという。特に、完全な熱力学函数のいずれかが1階微分不可能になるような相転移を1次相転移という。1次相転移の前後ではエントロピーの自然な変数のいずれかが不連続に変化し、その間、単一の平衡状態において複数の相が共存することができる。特に、自発的な対称性の破れ（@自発的な対称性の破れ）を伴う1次相転移では、その前後で秩序変数が不連続に変化する。

\
参考文献：

- 清水明『熱力学の基礎 II』

\

== 自発的な対称性の破れ <自発的な対称性の破れ>

#h(1em)統計力学において、ミクロ状態を記述するハミルトニアンが持っている対称性が、マクロな平衝状態に反映されないことがある。これを自発的な対称性の破れという。

例えば、外部磁場のないイジング模型（@イジング模型）では、ハミルトニアンはスピンを一斉に反転させる変換に対する対称性を持つ。高温の平衡状態では磁化が0であり、スピン反転対称性が保たれているが、転移温度よりも低温では自発的に有限の磁化が生じ、スピン反転対称性が破れている。このように、相転移の多くは自発的な対称性の破れを伴い、対称性が破れている相を秩序相、破れていない相を無秩序相という。イジング模型における磁化のように、無秩序相では0となり、秩序相では0でない値を持つ相加変数を秩序変数という。エントロピーの自然な変数の組を、秩序変数を含むようにとれば、無秩序相のエントロピーはそこから秩序変数を除いた変数の組で表せることになる。

他の例として、ハイゼンベルク模型におけるスピン回転対称性の破れや、気体--固体相転移における連続並進対称性の破れがある。これらはイジング模型とは異なり、破れているのは連続的な対称性である。この場合、秩序相にあっても、平衡を保ちながら破れた対称性の間で連続的な変換を行うことができる。これを南部--ゴールドストーン・モードという。

\
参考文献：

- 高橋和孝・西森秀稔『相転移・臨界現象とくりこみ群』

\

== 電磁場のエネルギー（2） <電磁場のエネルギー2>

- 物質中の電磁場のエネルギー

  @電磁場のエネルギー1 に記す。

- 黒体輻射

  温度 $T$ の平衡状態にある電磁場を考える。1光子状態は波数 $bold(k)$ と偏光 $lambda in {1 , 2}$ で指定される。空間を体積 $V = L^3$ の立方体の内部に制限し、周期境界条件を課すと、波数が取り得る値は $
    bold(k) = (2 pi)/L bold(n) , quad bold(n) in ZZ^3
  $ となる。状態 $(bold(k) , lambda)$ の光子が $n$ 個あるときのエネルギーは $hbar omega_(bold(k) , lambda) n$ で与えられるから#footnote[
    調和振動子としてエネルギー固有値を求めると $hbar omega_(bold(k) , lambda) (n + 1/2)$ となるが、ここでは基底状態（真空）のエネルギーを0としないと分配函数が発散してしまう。
  ]、状態 $(bold(k) , lambda)$ の分配函数は $
    z_(bold(k) , lambda) (beta) = sum_(n = 0)^oo "e"^(- beta hbar omega_(bold(k) , lambda) n) = 1/(1 - "e"^(- beta hbar omega_(bold(k) , lambda)))
  $ となり、状態 $(bold(k) , lambda)$ のエネルギー期待値は $
    expval(u_(bold(k) , lambda)) = - 1/(z_(bold(k) , lambda) (beta)) pdv(z_(bold(k) , lambda) (beta), beta) = (hbar omega_(bold(k) , lambda))/("e"^(beta hbar omega_(bold(k) , lambda)) - 1)
  $ となる。$omega_(bold(k) , lambda) <= omega$ となるような $(bold(k) , lambda)$ の個数は $
    Omega (omega) = (4 pi)/3 ((omega L)/(2 pi c))^3 dot 2
  $ であるから、エネルギー密度スペクトルは $
    epsilon (omega) dif omega = 1/V (hbar omega)/("e"^(beta hbar omega) - 1) dif Omega (omega) = (hbar omega^3)/(pi^2 c^3 ("e"^(beta hbar omega) - 1)) dif omega
  $ となる。これをプランクの放射公式という。内部エネルギー密度は $
    u = integral_0^oo epsilon (omega) dif omega = 1/(pi^2 hbar^3 c^3 beta^4) integral_0^oo x^3/("e"^x - 1) dif x = pi^2/(15 hbar^3 c^3 beta^4)
  $ となり、温度の4乗に比例する。これをシュテファン--ボルツマンの法則という。

  // 単位体積あたりのヘルムホルツ・エネルギーは $
  //   f (beta) & = - 1/(beta L^3) ln Z (beta) \
  //   & = - 1/(beta L^3) integral_0^oo ln (1/(1 - "e"^(- beta hbar omega))) dif Omega (omega) \
  //   & =  - 1/(beta L^3) ([ln (1/(1 - "e"^(- beta hbar omega))) Omega (omega)]_(omega = 0)^oo + integral_0^oo (beta hbar)/("e"^(beta hbar omega) - 1) Omega (omega) dif omega) \
  //   & = - 1/(6 pi^2 hbar^3 c^3 beta^4) integral_0^oo x^3/("e"^x - 1) dif x
  // $

\

== 熱力学第2法則

#h(1em)現代的な熱力学は大まかには以下の2つを原理とする。

+ 平衡状態は与えられた拘束条件を満たす状態のうちエントロピーが最大のものである。

+ 系は時間が経つと平衡状態に移行する。

#h(1em)これらの原理から、熱力学的な変化によって孤立系のエントロピーが減少しないことが導かれる。これを熱力学第2法則といい、熱力学において実現可能な過程を特徴付ける重要な法則である。歴史的には、この法則の表現として以下のようなものが発見されてきた。

- クラウジウスの法則： 低温の熱源から高温の熱源に正の熱を移すためには正の仕事が必要である。

- トムソンの法則： 1つの熱源から正の熱を受け取り、それを全て仕事に変換するサイクルは存在しない。

- カラテオドリの原理： 任意の平衝状態に対して、その任意の近傍に、その状態からの断熱変化で到達できない平衡状態が存在する。

#h(1em)これらの表現は全て等価であることが示されている。非平衡熱力学では以下の対応する定理が得られている。

- ジャルジンスキー等式： 熱浴に接した系が受け取る仕事を $W$, ヘルムホルツ・エネルギー変化を $Delta F$ とすると、$expval("e"^(- beta W)) = "e"^(- beta Delta F)$ が成り立つ（$expval(dotproduct)$ はアンサンブル平均を表す）。

- ゆらぎの定理： エントロピー生成が $sigma$ となる確率を $Pr (sigma)$ とすると、$(Pr (sigma))/(Pr (- sigma)) = "e"^sigma$ が成り立つ。

#h(1em)ゆらぎの定理から $expval("e"^(- sigma)) = 1$ が得られ、これはジャルジンスキー等式と等価である。さらにイェンゼンの不等式を用いると熱力学第2法則が導かれる。

\
参考文献：

- 清水明『熱力学の基礎 I』

\

== 平均場近似 <平均場近似>

#h(1em)平均場近似では、多数の粒子が相互作用している系を、平均的な場を感じる独立な1粒子の集まりとして近似する。例として、強磁性相互作用 $J > 0$ を持つイジング模型（@イジング模型）を考える#footnote[
  　反強磁性相互作用のときは副格子ごとにスピンの平均値の符号を逆転させて考える必要がある。
]。スピンの平均値が位置 $j$ によらずに $expval(sigma_j) = m$ であるとして、ハミルトニアンを $
  H & = - J sum_expval(j "," k) sigma_j sigma_k - h sum_j sigma_j \
  & tilde.eq - J sum_expval(j "," k) (sigma_j m + m sigma_k - m^2) - h sum_j sigma_j \
  & = (z J m^2 N)/2 - (z J m + h) sum_j sigma_j
$ と近似する。ここで、$z$ は配位数（$d$ 次元立方格子では $z = 2 d$）、$N$ は格子点の総数である。このとき、疑似分配函数は $
  tilde(Z) (beta ; m) & = "e"^(- beta z J m^2 N \/ 2) product_j (sum_(sigma_j = plus.minus 1) "e"^(- beta (z J m + h) sigma_j)) \
  & = (2 "e"^(- beta z J m^2 \/ 2) cosh (beta (z J m + h)))^N
$ と計算できる。平衡状態においては $tilde(Z) (beta ; m)$ を最大にするような $m$ が実現する。格子点あたりの疑似自由エネルギーは $
  tilde(g) (beta , h ; m) & = - 1/(beta N) ln tilde(Z) (beta ; m) \
  & = (z J m^2)/2 - 1/beta ln (2 cosh (beta (z J m + h)))
$ となる。$m$ は $tilde(g) (beta , h ; m)$ を最小にするから、$
  pdv(tilde(g) (beta , h ; m) , m) = 0 sp & <==> sp z J m - z J tanh (beta (z J m + h)) = 0 \
  & <==> sp m = tanh (beta (z J m + h))
$ が成り立つ。これを $m$ に関する自己無撞着方程式という。

// $m$ は格子点あたりの磁化に等しいはずだから、平衡状態においては $
//   m & = - pdv(g (beta , h) , h) \
//   & = tanh (beta (z J m + h)) - z J (m - tanh (beta (z J m + h))) pdv(m (beta , h), h)
// $ $
//   <==> sp m = tanh (beta (z J m + h))
// $ が成り立つ。これを $m$ に関する自己無撞着方程式という。

$tilde(g) (beta , h ; m)$ を最小にする $m$ の値を $T$, $h$ の函数として図示すると図@ising_mag のようになる。$T >= T_upright(c) := (z J)/k_upright(B)$ のとき、自己無撞着方程式の解はただ1つであり、特に $h = 0$ のとき $m = 0$ となる。一方、$T < T_upright(c)$, $h = 0$ のときは、それ以外にも解が正負に1つずつ存在する。$tilde(g) (beta , h ; m)$ を最小にするのは2つの非零の解であり、そのどちらかが実現される（自発的な対称性の破れ（@自発的な対称性の破れ）という）。$T < T_upright(c)$ では $h$ の正負によって $m$ が不連続に変化し、1次相転移があるという。相境界の端点 $(T = T_upright(c) , h = 0)$ を臨界点という。臨界点では $m$ の傾きが発散し、2次相転移があるという。

#figure(
  image("ising_mag.jpeg", width: 7.5cm),
  caption: [
    $m (T , h)$ のグラフ。$x$, $y$, $z$ 軸はそれぞれ $T$, $h$, $m$ を表す。グラフはDesmos 3D Calculatorにより作成した。
  ]
) <ising_mag>

#h(1em)自己無撞着方程式を逆に解くことで、ヘルムホルツ・エネルギーを $
  f (beta , m) & = g (beta , h (beta , m) ; m) + m h (beta , m) \
  & = (z J m^2)/2 - 1/beta ln (2/sqrt(1 - m^2)) + m (1/beta tanh^(- 1) m - z J m) \
  & = - (z J m^2)/2 - 1/beta (- (1 + m)/2 ln ((1 + m)/2) - (1 - m)/2 ln ((1 - m)/2))
$ と求めることができる。この $f (beta , m)$ は $T < T_upright(c)$ かつ $abs(m)$ が小さいときに $m$ に関する凸性を満たさないが、これは $m$ が位置によらないという仮定が破綻することを意味しており、実際の系では $m$ が正の領域と負の領域に分離することになる。これを相共存といい、1次相転移（@一次相転移）に特有の現象である（図@ising_f）。

#figure(
  {
    box(image("ising_f_1.jpeg", width: 7.5cm))
		h(1cm)
    box(image("ising_f_2.jpeg", width: 7.5cm))
  },
  caption: [
    （左）平均場近似による $f (T , m)$ のグラフ。$x$, $y$, $z$ 軸はそれぞれ $T$, $m$, $f$ を表す。（右）$m$ に関する凸性を満たすように修正したもの。修正した領域（青色で示されている）では相共存が起こっていると解釈される。グラフはDesmos 3D Calculatorにより作成した。
  ]
) <ising_f>

#h(1em)このように、平均場近似によって系の定性的な振る舞いを説明することができる。

\
参考文献：

- 高橋和孝・西森秀稔『相転移・臨界現象とくりこみ群』

\

== ボース--アインシュタイン凝縮

#h(1em)粒子数 $N$ が保存するようなボース粒子からなる系を考える。1粒子状態は量子数 $j$ によって指定されるとし、そのエネルギー固有値を $epsilon_j$ とする。基底状態のエネルギーを $epsilon_0$ とする。状態 $j$ の大分配函数は $
  xi_j (beta , mu) = sum_(n = 0)^oo "e"^(- beta (epsilon_j n - mu n)) = 1/(1 - "e"^(- beta (epsilon_j - mu)))
$ となる（全ての $j$ に対して $xi_j (beta , mu)$ が収束するために、$mu < epsilon_0$ である必要がある）。状態 $j$ にある粒子数の期待値は $
  expval(n_j) = 1/(beta xi_j (beta , mu)) pdv(xi_j (beta , mu), mu) = 1/("e"^(beta (epsilon_j - mu)) - 1)
$ となる。全粒子数 $N$ を指定した場合、等式 $
  N = sum_j expval(n_j)
$ が成り立つように $mu$ の値が決まるが、もし $epsilon_0 - mu$ がマクロに見て0になれば、基底状態の粒子数 $N_0$ はマクロな量になる。これをボース--アインシュタイン凝縮という。

$epsilon_j <= epsilon$ となるような $j$ の個数を $Omega (epsilon)$ とすると、右辺の無限和は $
  N = N_0 + integral_0^oo 1/("e"^(beta (epsilon - mu)) - 1) dif Omega (epsilon)
$ と表される。$mu < epsilon_0$ のとき、（マクロに見て）$N_0 = 0$ であるから、$
  N = integral_0^oo 1/("e"^(beta (epsilon - mu)) - 1) dif Omega (epsilon) < integral_0^oo 1/("e"^(beta (epsilon - epsilon_0)) - 1) dif Omega (epsilon)
$ が（最右辺の積分が収束するならば）成り立つ。この不等式が破れるとき、$mu = epsilon_0$ となってボース--アインシュタイン凝縮が起こり、$
  N_0 = N - integral_0^oo 1/("e"^(beta (epsilon - epsilon_0)) - 1) dif Omega (epsilon)
$ となる。

ボース--アインシュタイン凝縮が起こる具体的な系として、3次元理想ボース気体がある。スピン0の3次元理想ボース気体の1粒子状態は波数 $bold(k)$ で指定される。空間を体積 $V = L^3$ の立方体の内部に制限し、周期境界条件を課すと、波数が取り得る値は $
  bold(k) = (2 pi)/L bold(n) , quad bold(n) in ZZ^3
$ となる。波数 $bold(k)$ の1粒子のエネルギーは $
  epsilon_bold(k) = hbar^2/(2 m) abs(bold(k))^2
$ で与えられ、特に基底状態のエネルギーは $epsilon_0 = 0$ である。$epsilon_bold(k) <= epsilon$ となるような $bold(k)$ の個数は $
  Omega (epsilon) = (4 pi)/3 ((sqrt(2 m epsilon) L)/(2 pi hbar))^3
$ となるから、ボース--アインシュタイン凝縮が起こらないための条件は $
  N & < integral_0^oo 1/("e"^(beta epsilon) - 1) dif Omega (epsilon) \
  & = (m^(3 \/ 2) V)/(sqrt(2) pi^2 hbar^3) integral_0^oo sqrt(epsilon)/("e"^(beta epsilon) - 1) dif epsilon \
  & = (m^(3 \/ 2) V)/(sqrt(2) pi^2 hbar^3 beta^(3 \/ 2)) integral_0^oo sqrt(x)/("e"^x - 1) dif x = (zeta (3/2) m^(3 \/ 2) V)/(2 sqrt(2) pi^(3 \/ 2) hbar^3 beta^(3 \/ 2))
$ となる。したがって、転移温度は $
  T_upright(c) = (2 pi hbar^2 N^(2 \/ 3))/(zeta (3/2)^(2 \/ 3) k_upright(B) m V^(2 \/ 3))
$ で与えられる。$T < T_upright(c)$ のとき、基底状態の粒子数は $
  N_0 = N - (zeta (3/2) m^(3 \/ 2) V)/(2 sqrt(2) pi^(3 \/ 2) hbar^3 beta^(3 \/ 2)) = N (1 - (T/T_upright(c))^(3 \/ 2))
$ となる。

\

== 臨界現象

#h(1em)...

\
参考文献：

- 高橋和孝・西森秀稔『相転移・臨界現象とくりこみ群』

#pagebreak()

= 固体物理学

== 金属と絶縁体

#h(1em)...

\

== 固体の比熱

#h(1em)固体の比熱は主に格子比熱と電子比熱の和である。格子比熱はボソンであるフォノンの寄与による比熱であり、例えばデバイ模型（@デバイ周波数）によって説明される。デバイ温度（通常、室温と同程度）よりも十分低温では $T^3$ に比例する。電子比熱はフェルミオンである電子の寄与による比熱であり、低温の金属において特に重要である。金属の電子比熱は例えば自由電子模型によって説明され、フェルミ温度（通常、室温よりも十分大きい）よりも十分低温では $T$ に比例する。絶縁体では伝導帯（@バンド理論）にある電子の数が低温で指数函数的に少なくなるため、電子比熱は低温において無視できる。室温では絶縁体と金属でともに格子比熱が支配的である。

\

== 超伝導

#h(1em)...

\

== デバイ周波数 <デバイ周波数>

#h(1em)結晶中のフォノンの内部エネルギーを黒体輻射（@電磁場のエネルギー2）と同様の方法で求める。1フォノン状態は波数 $bold(k)$ と偏光 $lambda in {1 , 2 , 3}$（2つの横波と1つの縦波）で指定される。簡単のために、結晶は立方格子であり、格子定数は $a$ であるとする。さらに、空間を体積 $V = L^3$ の立方体に制限し、周期境界条件を課すと、波数が取り得る値は第1ブリルアン・ゾーン（@ブリルアン・ゾーン）内に制限され、$
  bold(k) in [- pi/a , pi/a]^3 , quad bold(k) = (2 pi)/L bold(n) , quad bold(n) in ZZ^3
$ となる。これにより、取り得る波数は全部で $N = (L/a)^3$ 通りとなる。フォノンの分散関係を $
  omega_(bold(k) , lambda) tilde.eq c_upright(s) abs(bold(k))
$ と近似する（この近似は低エネルギーでよく成り立つ）。状態 $(bold(k) , lambda)$ のフォノンが $n$ 個あるときのエネルギーは $hbar omega_(bold(k) , lambda) n$ で与えられるから、状態 $(bold(k) , lambda)$ の分配函数は $
  z_(bold(k) , lambda) (beta) = sum_(n = 0)^oo "e"^(- beta hbar omega_(bold(k) , lambda) n) = 1/(1 - "e"^(- beta hbar omega_(bold(k) , lambda)))
$ となる。状態 $(bold(k) , lambda)$ のエネルギー期待値は $
  expval(u_(bold(k) , lambda)) = - 1/(z_(bold(k) , lambda) (beta)) pdv(z_(bold(k) , lambda) (beta), beta) = (hbar omega_(bold(k) , lambda))/("e"^(beta hbar omega_(bold(k) , lambda)) - 1)
$ となる。内部エネルギー $
  U = sum_(bold(k) , lambda) expval(u_(bold(k) , lambda))
$ を計算する。和を取る領域は第1ブリルアン・ゾーンであるが、これを周波数が $omega_upright(D)$ 以下となる領域 ${(bold(k) , lambda) mid(|) omega_(bold(k) , lambda) <= omega_upright(D)}$ によって近似する。$omega_upright(D)$ を状態数が $3 N$ に保たれるように選ぶと、$
  (4 pi)/3 ((omega L)/(2 pi c_upright(s)))^3 dot 3 = 3 N sp <==> sp omega_upright(D) = (2 pi c_upright(s))/L ((3 N)/(4 pi))^(1 \/ 3) = (6 pi^2)^(1 \/ 3) c_upright(s)/a
$ となる。これをデバイ周波数という。$omega_(bold(k) , lambda) <= omega$ となるような $(bold(k) , lambda)$ の個数は $
  Omega (omega) = 3 N (omega/omega_upright(D))^3
$ となるから、内部エネルギーは $
  U & tilde.eq integral_0^omega_upright(D) (hbar omega)/("e"^(beta hbar omega) - 1) dif Omega (omega) \
  & = (9 N)/(omega_upright(D)^3) integral_0^omega_upright(D) (hbar omega^3)/("e"^(beta hbar omega) - 1) dif omega \
  & = (9 N)/(hbar^3 omega_upright(D)^3 beta^4) integral_0^(beta hbar omega_upright(D)) x^3/("e"^x - 1) dif x
$ となり、定積熱容量は $
  C_V = pdv(U, T) & = - k_upright(B) beta^2 dv(, beta) ((9 N)/(omega_upright(D)^3) integral_0^omega_upright(D) (hbar omega^3)/("e"^(beta hbar omega) - 1) dif omega) \
  & = (9 k_upright(B) beta^2 N)/(omega_upright(D)^3) integral_0^omega_upright(D) (hbar^2 omega^4 "e"^(beta hbar omega))/("e"^(beta hbar omega) - 1)^2 dif omega \
  & = (9 k_upright(B) N)/(hbar^3 omega_upright(D)^3 beta^3) integral_0^(beta hbar omega_upright(D)) (x^4 "e"^x)/("e"^x - 1)^2 dif x
$ となる。デバイ温度を $T_upright(D) := (hbar omega_upright(D))/k_upright(B)$ により定めると、デバイの比熱式 $
  C_V = 9 k_upright(B) N (T/T_upright(D))^3 integral_0^(T_upright(D) \/ T) (x^4 "e"^x)/("e"^x - 1)^2 dif x
$ が得られる。$T << T_upright(D)$ では $
  C_V tilde.eq 9 k_upright(B) N (T/T_upright(D))^3 integral_0^oo (x^4 "e"^x)/("e"^x - 1)^2 dif x = (12 pi^4 k_upright(B) N)/5 (T/T_upright(D))^3 prop T^3
$ が成り立ち、$T >> T_upright(D)$ では $
  C_V tilde.eq 9 k_upright(B) N (T/T_upright(D))^3 integral_0^(T_upright(D) \/ T) x^2 dif x = 3 k_upright(B) N
$ が成り立つ。これらは多くの物質の比熱の振る舞いをよく説明する。

\

== 電子と正孔

#h(1em)...

\

== 電子比熱

#h(1em)...

\

== バンド理論 <バンド理論>

#h(1em)固体中の電子のハミルトニアンのスペクトル（固有値の集合）は漸近的に連続になる。これをバンド構造という。ブロッホの定理（@ブロッホの定理）より、エネルギー固有状態は波数により指定される。エネルギー固有値と波数の分散関係を波数空間（特に第1ブリルアン・ゾーン（@ブリルアン・ゾーン））上にプロットしたものを考えることが多い。

例えば、格子定数 $a$ を持つ1次元結晶において、ポテンシャルを0で近似する空格子近似を行うと、分散関係は $
  E = hbar^2/(2 m) (k - (2 pi n)/a)^2 , quad n in ZZ
$ となる。空格子近似ではハミルトニアンのスペクトルは非負の実数全体になるが、ポテンシャルを摂動として考慮に入れると、エネルギー固有値が互いから遠ざかるようにシフトすることによって、エネルギー固有値にならない区間が生じる。これをバンドギャップという。

電子のフェルミ準位（絶対零度極限における化学ポテンシャル）よりもエネルギーが低いバンドを価電子帯、それよりもエネルギーが高いバンドを伝導帯という。

絶縁体と金属の違いはバンド理論によって説明される。絶縁体ではフェルミ準位がバンドギャップ内にあり、価電子帯から伝導帯への励起には有限のエネルギーが必要である。一方、金属ではフェルミ準位がバンド内にあり、価電子帯から伝導帯に無限小のエネルギーで励起することができる。この違いが電気伝導度や比熱の違いを生んでいる。

\

== ブリルアン・ゾーン <ブリルアン・ゾーン>

#h(1em)基本格子ベクトル $bold(a)_1$, $bold(a)_2$, $bold(a)_3$ を持つ3次元結晶中の1電子状態を考える。整数 $n_1$, $n_2$, $n_3$ を用いて $bold(R) = n_1 bold(a)_1 + n_2 bold(a)_2 + n_3 bold(a)_3$ と表される $bold(R)$ を格子ベクトルという。ポテンシャルは周期性 $
  V (bold(x) + bold(R)) = V (bold(x))
$ を満たす。このとき、ブロッホの定理（@ブロッホの定理）より、ハミルトニアンの固有状態を、任意の格子ベクトル $bold(R)$ に対して $
  psi (bold(x) + bold(R)) = "e"^("i" bold(k) dot bold(R)) psi (bold(x))
$ を満たすように選ぶことができる。波数 $bold(k)$ が属する空間を波数空間という。波数空間上のベクトル $bold(b)_1$, $bold(b)_2$, $bold(b)_3$ を、$
  bold(a)_j dot bold(b)_k = 2 pi delta_(j k)
$ を満たすように定義する。整数 $m_1$, $m_2$, $m_3$ を用いて $bold(G) = m_1 bold(b)_1 + m_2 bold(b)_2 + m_3 bold(b)_3$ と表される $bold(G)$ を逆格子ベクトルという。任意の逆格子ベクトル $bold(G)$ と格子ベクトル $bold(R)$ に対して $"e"^("i" bold(G) dot bold(R)) = 1$ が成り立つから、$
  psi (bold(x) + bold(R)) = "e"^("i" bold(k) dot bold(R)) psi (bold(x)) sp <==> sp psi (bold(x) + bold(R)) = "e"^("i" (bold(k) + bold(G)) dot bold(R)) psi (bold(x))
$ 
となる。すなわち、波数 $bold(k)$ と $bold(k) + bold(G)$ は等価である。

第1ブリルアン・ゾーンは、波数空間において、逆格子点のうち原点までの距離が最も小さくなるような領域のことである。上に述べた波数の等価性から、結晶中の1電子状態を考えるときには、第1ブリルアン・ゾーンだけを考えれば十分である。

\

== ブロッホの定理 <ブロッホの定理>

#h(1em)任意の格子ベクトル $bold(R) = n_1 bold(a)_1 + n_2 bold(a)_2 + n_3 bold(a)_3$, $(n_1 , n_2 , n_3) in ZZ^3$ に対して、ポテンシャルが周期性 $
  V (bold(x) + bold(R)) = V (bold(x))
$ を満たすとする。このポテンシャル中の1電子のハミルトニアン $
  H = 1/(2 m) bold(p)^2 + V (bold(x))
$ の固有函数を、定数 $bold(k)$ を用いて、任意の格子ベクトル $bold(R)$ に対して $
  psi (bold(x) + bold(R)) = "e"^("i" bold(k) dot bold(R)) psi (bold(x))
$ を満たすように選ぶことができる。これをブロッホの定理という。

この定理の証明は以下のとおりである。並進演算子 $T_bold(R)$ を $
  T_bold(R) psi (bold(x)) = psi (bold(x) + bold(R))
$ により定義すると、$
  T_bold(R) (H (bold(x)) psi (bold(x))) = H (bold(x) + bold(R)) psi (bold(x) + bold(R)) = H (bold(x)) psi (bold(x) + bold(R)) = H (bold(x)) (T_bold(R) psi (bold(x)))
$ となるから、$[H , T_bold(R)] = 0$ が成り立つ。特に、$H$, $T_bold(a)_1$, $T_bold(a)_2$, $T_bold(a)_3$ は互いに交換する。したがって、これらの同時固有函数 $
  H psi (bold(x)) = E psi (bold(x))
$ $
  psi (bold(x) + bold(a)_1) = "e"^("i" theta_1) psi (bold(x))
$ $
  psi (bold(x) + bold(a)_2) = "e"^("i" theta_2) psi (bold(x))
$ $
  psi (bold(x) + bold(a)_3) = "e"^("i" theta_3) psi (bold(x))
$ を考えることができる。このとき、$bold(R) = n_1 bold(a)_1 + n_2 bold(a)_2 + n_3 bold(a)_3$ に対して、$
  psi (bold(x) + bold(R)) = "e"^("i" (n_1 theta_1 + n_2 theta_2 + n_3 theta_3)) psi (bold(x))
$ が成り立つ。そこで、$bold(k) dot bold(a)_j = theta_j$ が成り立つように $bold(k)$ を定義すれば、$
  psi (bold(x) + bold(R)) = "e"^("i" bold(k) dot bold(R)) psi (bold(x))
$ と表される。$abs(psi (bold(x)))$ が有界になるように、$bold(k)$ は実数となる。

\

== 有効質量

#h(1em)...
