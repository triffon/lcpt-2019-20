#lang racket

; протип:
; правете всичките си ламбди с един аргумент

; примери за естествени числа, кодирани чрез ламбда функции
; (чърч кодиране/нумерали на чърч)

; ще симулираме пеанови естествени числа, т.е. ето тази "дефиниция" на естествените числа

; 0. има нещо което се казва z и нещо което се казва s
; 1. z е естествено число
; 1. ако <нещо> е естествено число, то и (s <нещо>) също е естествено число

; с други думи искаме z да съответства на 0, а s на събиране с 1
; и всички останали естествени числа да представим като голям брой пъти 1 + 1 + 1 + 1 + ... 1 + 0
; (s брои колко пъти прибавяме 1)

; същото нещо ще направим и тук - броенето ни (s) ще е колко пъти сме приложили функция към аргумент
; а самият аргумент ще е "нулата"
; по конвенция винаги f ще ни е функцията която пролагаме а v ще кръщаваме константата която съответства на нула

; нула
(define czero
  (lambda (f)
    (lambda (v)
      v)))

; едно
(define cone
  (lambda (f)
    (lambda (v)
      (f v))))

; две
(define ctwo
  (lambda (f)
    (lambda (v)
      (f (f v)))))


; ПРИМЕРИ
(define 1+ (lambda (n) (+ 1 n)))

; разписване

; обръщане от и до
(define (nat-to-scm n)
  ((n 1+) 0))

; разписване

(define csucc
  (lambda (n)
    (lambda (f)
      (lambda (v)
        (f ((n f) v))))))

; разписване

; забележете че трябва два пъти да извикаме `n`, щото все пак са два ламбди и в скийм има разлика между
; A x A -> A
; и
; A -> (A -> A)

; грешно нарочно?
(define (nat-from-scm n)
  (if (= 0 n)
      czero
      (csucc (nat-from-scm (- n 1)))))

; "директен" vs "недиректен" подход
(define cplus
  (lambda (n)
    (lambda (m)
      (lambda (f)
        (lambda (v)
          ((n f) ((m f) v)))))))

; (nat-to-scm ((cplus ctwo) ctwo))
;n = cone = \f.\v. (f v)
;m = ctwo = \f.\v. (f (f v))
;cplus n m
;->
;\f.\v. cone f ctwo ->
;\f.\v. f ctwo ->
;
;\f.\v. f (f (f v))


; разписване?

(define cplus-another
  (lambda (n)
    (lambda (m)
      ((n csucc) m))))

; (nat-to-scm ((cplus (nat-from-scm 5)) (nat-from-scm 15)))
; (nat-to-scm ((cplus-another (nat-from-scm 5)) (nat-from-scm 15)))

; =====================
; foldr кодирани списъци (foldr-али???)

; show lists as a parallel with natural numbers
; in haskell
; data Nat = Zero | Succ Nat
;
; Zero
;
; (lambda (f)
;   (lambda (v)
;     v))
;
;
;  (Succ (Succ (Succ Zero)))
;
;  (lambda (f)
;    (lambda (v)
;      (f    (f    (f    v)))))
;       Succ (Succ (Succ Zero)
;
;
;data List = Nil | Cons Int List
;
; Nil
;
; k*
; (lambda (f)
;   (lambda (v)
;     v))
;
; Succ Zero
;
; (Cons 0 Nil)

; (lambda (f)
;   (lambda (v)
;     (f czero v)))
;
;
;(Cons 0 (Cons 1 (Cons 2 Nil)))

; (lambda (f)
;   (lambda (v)
;     ((f   0) ((f   1) ((f   2) v)))))
;     (Cons 0  (Cons 1  (Cons 2  Nil)))

(define cnil
  (lambda (f)
    (lambda (v)
      v)))

; (ccons cnil 1 ->
; (lambda (f)
;   (lambda (v)
;     ((f 1) v)))
; ((ccons 2) ((ccons 1) nil)) ->
; (lambda (f)
;   (lambda (v)
;     ((f 2) ((f 1) v))))

(define ccons
  (lambda (x)
    (lambda (xs)
      (lambda (f)
        (lambda (v)
          ((f x) ((xs f) v)))))))

; 1 2 3 -> 6
; '(1 2 3)

; ((+) 1 ((+) 2 ((+) 3 0)))
; (f   1 (f   2 (f   3 v)))
; f -> cplus
; v -> czero

(define csum
  (lambda (xs)
    ((xs cplus) czero)))


; =====================
; Нумерали на Чърч

; УПРАЖНЕНИЕ: Умножение
; ПРИМЕРИ:
; (nat-to-scm ((cmult (nat-from-scm 1)) (nat-from-scm 3))) -- 3
; (nat-to-scm ((cmult (nat-from-scm 1)) (nat-from-scm 0))) -- 0
; (nat-to-scm ((cmult (nat-from-scm 23)) (nat-from-scm 3))) -- 69
; (nat-to-scm ((cmult (nat-from-scm 21)) (nat-from-scm 2))) -- 42
(define cmult
  (lambda (n)
    (lambda (m)
      ((m (cplus n)) czero))))

; УПРАЖНЕНИЕ: Повдигане на степен
; ПРИМЕРИ:
; (nat-to-scm ((cexp (nat-from-scm 3)) (nat-from-scm 1))) -- 3
; (nat-to-scm ((cexp (nat-from-scm 2)) (nat-from-scm 10))) -- 1024
; (nat-to-scm ((cexp (nat-from-scm 0)) (nat-from-scm 10))) -- 0
; (nat-to-scm ((cexp (nat-from-scm 30)) (nat-from-scm 0))) -- 0
(define cexp
  (lambda (n)
    (lambda (m)
      ((m (cmult n)) cone))))

; =====================
; Чърч кодирани булеви стойности (бинерали на Чърч?)

; true
(define ctt
  (lambda (t)
    (lambda (f)
      t)))

; false
(define cff
  (lambda (t)
    (lambda (f)
      f)))

; if
(define cif
  (lambda (b)
    (lambda (t)
      (lambda (e)
        ((b t) e)))))


; УПРАЖНЕНИЕ: Конвертиране от бинерали към булеви стойности на скийм
; ПРИМЕРИ:
; (bool-to-scm ctt) -- #t
; (bool-to-scm cff) -- #f
(define (bool-to-scm b)
  ((b #t) #f))

; УПРАЖНЕНИЕ: Конвертиране от булеви стойности на скийм към бинерали
; ПРИМЕРИ:
; (((bool-from-scm #t) 5) 3) -- 5
; (((bool-from-scm #f) 5) 3) -- 3
(define (bool-from-scm b)
  (if b ctt cff))

; УПРАЖНЕНИЕ: Отрицание на булеан
; ПРИМЕРИ:
; (bool-to-scm (cnot ctt)) -- #f
; (bool-to-scm (cnot (cnot ctt))) -- #t
(define cnot
  (lambda (b)
    ((b cff) ctt)))

; УПРАЖНЕНИЕ: Четност
; ПРИМЕРИ:
; (bool-to-scm (ceven (nat-from-scm 0))) -- #t
; (bool-to-scm (ceven (nat-from-scm 1337))) -- #f
; (bool-to-scm (ceven (nat-from-scm 8))) -- #t
(define ceven
  (lambda (n)
    ((n cnot) ctt)))

; =====================
; СПИСЪЦИ
; тук можете да ползвате и скиймски стойности вътре в списъците!
; по-лесно е за тестване понякога

; УПРАЖНЕНИЕ: Произведението на числата в списък
; ПРИМЕРИ:
; (nat-to-scm (cprod cnil)) -- 1
; (nat-to-scm (cprod ((ccons ctwo) ((ccons ctwo) cnil)))) -- 4
; (nat-to-scm (cprod ((ccons ctwo) ((ccons ctwo) ((ccons ctwo) cnil))))) -- 8
(define cprod
  (lambda (xs)
    ((xs cmult) cone)))
; HINT: Откраднете вдъхновение от csum

; Полезно за после:
; Функция която взима три аргумента и връща първия.
(define k3
  (lambda (x)
    (lambda (y)
      (lambda (z)
        x))))

; УПРАЖНЕНИЕ: Проверка за празен списък
; Проверете дали подаденият списък е празен.
; Имайте предвид колко аргумента взимат функциите в нашето представяне на списъци.
; ПРИМЕРИ:
; (bool-to-scm (cnil? cnil)) -- #t
; (bool-to-scm (cnil? ((ccons cnil) cnil))) -- #f
(define cnil?
  (lambda (xs)
    ((xs (k3 cff)) ctt)))

; Полезно за после:
; Скиймският `cons`, но curry-нат.
(define curried-cons
  (lambda (x) (lambda (y) (cons x y))))

; УПРАЖНЕНИЕ: Конвертирайте foldr-ал към скиймски списък
; ПРИМЕРИ:
; (list-to-scm cnil) -- '()
; (list-to-scm ((ccons 6) cnil)) -- '(6)
; (list-to-scm ((ccons 6) ((ccons 9) cnil))) -- '(6 9)
(define (list-to-scm xs)
  ((xs curried-cons) '()))
; HINT:
; Възползвайте се от структурата на foldr-алите, както се възползвахме от
; структурата при естествените числа за съответната ѝ функция!

; УПРАЖНЕНИЕ: Конвертирайте от скийсмки списък към foldr-ал
; ПРИМЕРИ:
; (list-to-scm (list-from-scm '(0))) -- '(0)
; (list-to-scm (list-from-scm '(1))) -- '(1)
; (list-to-scm (list-from-scm '(1 3 3 7))) -- '(1 3 3 7)
(define (list-from-scm xs)
  (if (empty? xs)
      cnil
      ((ccons (car xs)) (list-from-scm (cdr xs)))))
; HINT:
; Използвайте cnil и ccons

; УПРАЖНЕНИЕ: Дължина на foldr-ал
; ПРИМЕРИ:
; (nat-to-scm (clength (list-from-scm '()))) -- 0
; (nat-to-scm (clength (list-from-scm '(1 2)))) -- 2
(define clength
  (lambda (xs)
    ((xs (lambda (x) csucc)) czero)))

; УПРАЖНЕНИЕ: Генериране на списък с нумералите от подадения нумерал до cnil
; (редът не е задължително да е нарастващ или намаляващ)
; ПРИМЕРИ:
; (nat-to-scm (clength (cto-zero (nat-from-scm n)))) -- n
; (map nat-to-scm (list-to-scm (cto-zero (nat-from-scm 10)))) -- '(9 8 7 6 5 4 3 2 1 0)
; (list-to-scm (cto-zero (nat-from-scm 0))) -- '()
(define cto-zero
  (lambda (n)
    ((n (lambda (r) ((ccons (clength r)) r))) cnil)))

; HINT:
; Помислете как да да използвате "резултата от рекурсивното извикване",
; което ви предоставя нумералът n като аргумент, за да разберете "на кое естествено число сте в момента".
;
; С други думи - представете си че сте извикали
; (cto-zero 3)
; "рекурсивното извикване", което се случва имплицитно, благодарени на нумералите ще е
; (cto-zero 2), което ще ви даде '(1 0)
; Искате резултатът на (cto-zero 3) да е '(2 1 0)
; Как може използвайки информация за списъка '(1 0) да стигнете до списъка '(2 1 0)?

; УПРАЖНЕНИЕ: foldr за foldr-али
; ПРИМЕР:
; (nat-to-scm (((cfoldr cplus) czero) ((ccons ctwo) ((ccons (csucc ctwo)) cnil)))) -- 5
(define cfoldr
  (lambda (f)
    (lambda (v)
      (lambda (xs)
        ((xs f) v)))))
; HINT: Откраднете вдъхновение от това как cif се отнася към бинералите.

; Може би полезно за после.
(define compose (lambda (f) (lambda (g) (lambda (x) (f (g x))))))

; УПРАЖНЕНИЕ: map за foldr-али
; ПРИМЕРИ:
; (list-to-scm ((cmap 1+) (list-from-scm '(1 2 3)))) -- '(2 3 4)
; (map nat-to-scm (list-to-scm ((cmap csucc) (list-from-scm (map nat-from-scm '(41 68)))))) -- '(42 69)
(define cmap
  (lambda (f)
      ((cfoldr (lambda (x) (lambda (r) ((ccons (f x)) r)))) czero)))
; HINT: Помислете как да реализирате map използвайки foldr

; УПРАЖНЕНИЕ: Факториел
; Възползвайте се от cto-zero и cprod
; ПРИМЕРИ:
; (nat-to-scm (cfact (nat-from-scm 0))) -- 1
; (nat-to-scm (cfact (nat-from-scm 5))) -- 120
; (nat-to-scm (cfact (nat-from-scm 10))) -- 3628800

; AUTHOR'S NOTE: Но аз ще се възползвам и от cmap, щото ми изглежда най-изчистено.
(define cfact
  (lambda (n)
    (cprod ((cmap csucc) (cto-zero n)))))

(define i (lambda (x) x))

; УПРАЖНЕНИЕ: filter за foldr-али
; Приемете че подадената функция връща бинерал.
; ПРИМЕР:
; (map nat-to-scm (list-to-scm ((cfilter ceven) (cto-zero (nat-from-scm 10))))) -- '(10 8 6 4 2)
(define cfilter
  (lambda (p)
    ((cfoldr
      (lambda (x)
        (((p x) (ccons x)) i)))
      cnil)))
; HINT: Помислете как да реализирате filter използвайки foldr.

; УПРАЖНЕНИЕ: foldl за foldr-али (uh-oh)
; Помислете как да имплементиранте foldl чрез foldr, използвайки композиция на функции като операцията за сгъване.

; AUTHOR'S NOTE: Първо на Haskell:
;
; flip :: (a -> b -> c) -> (b -> a -> c)
; flip f x y = f y x
;
; foldl :: (b -> a -> b) -> b -> [a] -> b
; foldl f v xs = (foldr (\x r -> r . flip f x) id xs) v -- същото като
; foldl f v xs = foldr (\x r -> r . flip f x) id xs v
; Тоест: натрупване *функции*, като внимаваме натрупването да става *отляво* - "като ми дадеш начална стойност ще изпълня всички тези натрупани функции"
; и чак накрая даваме началната стойност, за да можем да я сложим отляво.

; Разписано:
; foldl f v xs
; foldr (\x r -> r . flip f x) id [1,2,3] v
; (foldr (\x r -> r . flip f x) id [1,2,3]) v
; ((foldr (\x r -> r . flip f x) id [2,3]) . flip f 1) v
; (((foldr (\x r -> r . flip f x) id [3]) . flip f 2) . flip f 1) v
; ((((foldr (\x r -> r . flip f x) id []) flip f 3) . flip f 2) . flip f 1) v
; (((id . flip f 3) . flip f 2) . flip f 1) v
; (((flip f 3) . flip f 2) . flip f 1) v
; ((flip f 3) . flip f 2) (flip f 1 v)
; ((flip f 3) . flip f 2) (f v 1)
; (flip f 3) (flip f 2 (f v 1))
; (flip f 3) (f (f v 1) 2)
; flip f 3 (f (f v 1) 2)
; f (f (f v 1) 2) 3

; Което е точно лявo-скобуваният еквивалент на
; foldr f v [1,2,3]
; което произвежда
; f (1 (f 2 (f 3 v)))


; Как го измислих това?
; 0. (главно това) Виждал съм го вече.
; 1. Главната разлика на foldr и foldl е в това че едното е скобувано "надясно", а другото "наляво".
; Аз искам да направя от едното другото - тоест да променя къде седят скобите.
; Има ли нещо което ми позволява да местя скоби както си искам? Операцията на моноид - тя е асоциативна.
; За какви моноиди се сещам - функции от тип (a -> a)
; каквато е именно (flip f x)
; Понеже още си мисля за моноиди се сещам че неутралната му операция е
; id :: a -> a
; id x = x
; Магически измислям останалото, като внимавам скобите да са както ми трябват.

(define cflip
  (lambda (f)
    (lambda (x)
      (lambda (y)
        ((f y) x)))))

(define cfoldl
  (lambda (f)
    (lambda (v)
      (lambda (xs)
        ((((cfoldr (lambda (x) (lambda (r) ((compose r) ((cflip f) x))))) i) xs) v)))))

; УПРАЖНЕНИЕ: reverse за foldr-али (uh-oh)
; Помислете как да имплементиранте reverse чрез foldl
(define creverse
  (lambda (xs)
    (((cfoldl (cflip ccons)) cnil) xs)))

; или ета-редуцирано
(define creverse-eta
  ((cfoldl (cflip ccons)) cnil))