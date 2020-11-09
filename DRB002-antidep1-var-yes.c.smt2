

(declare-sort Char)
(define-sort Str () (Array Int Char))
(echo "Simulating signed 128 bit number domain...")
(echo "(including GNU C int128 (2's complement) and IEEE 754 binary128 overflow but excluding underflow)")
(echo "(https://gcc.gnu.org/onlinedocs/gcc/Integers-implementation.html#Integers-implementation)")
(echo "(https://gcc.gnu.org/onlinedocs/gcc/_005f_005fint128.html#g_t_005f_005fint128)")
(echo "(https://en.wikipedia.org/wiki/Quadruple-precision_floating-point_format#IEEE_754_quadruple-precision_binary_floating-point_format:_binary128)")
(define-fun MAX_MAX_INT () Int 9223372036854775807)  ;RangeDegradeMAX
(declare-fun MAX_INT () Int)                  ;RangeDegradeParam
(define-fun MIN_MAX_INT () Int 0)                     ;RangeDegradeMIN
(define-fun MIN_INT () Int (- (- MAX_INT) 1))
(define-fun MAX_REAL () Real (* (^ 2.0 1023) (- 2.0 (^ 2.0 (- 52)))))
(define-fun MIN_REAL () Real (- MAX_REAL))
;avoiding +/-/*/division/modulo overflow
(define-fun add_guard ((_1 Int)(_2 Int)) Bool (and 
	(<= MIN_INT _1)(<= _1 MAX_INT)
	(<= MIN_INT _2)(<= _2 MAX_INT)
	(<= MIN_INT (+ _1 _2))(<= (+ _1 _2) MAX_INT)
	))
(define-fun sub_guard ((_1 Int)(_2 Int)) Bool (and 
	(<= MIN_INT _1)(<= _1 MAX_INT)
	(<= MIN_INT _2)(<= _2 MAX_INT)
	(<= MIN_INT (- _1 _2))(<= (- _1 _2) MAX_INT)
))
(define-fun mul_guard ((_1 Int)(_2 Int)) Bool (and 
	(<= MIN_INT _1)(<= _1 MAX_INT)
	(<= MIN_INT _2)(<= _2 MAX_INT)
	(<= MIN_INT (* _1 _2))(<= (* _1 _2) MAX_INT)
))
(define-fun div_guard ((_1 Int)(_2 Int)) Bool (and 
	(not (= _2 0))
	(<= MIN_INT _1)(<= _1 MAX_INT)
	(<= MIN_INT _2)(<= _2 MAX_INT)
))
(define-fun mod_guard ((_1 Int)(_2 Int)) Bool (and 
	(div_guard _1 _2)
))
(declare-datatypes (PT_) ((Pointer 
				NULL
				Void
				(prim (value PT_))
				(ptr (addr Pointer)))))
(declare-sort PT)
(declare-sort Void)

(declare-fun i2pt (Int) PT)
(declare-fun r2pt (Real) PT)
(declare-fun b2pt (Bool) PT)
(define-fun point ((_p (Pointer PT))) (Pointer PT) 
				  (ite (is-ptr _p) (addr _p) _p) 
) 
(declare-fun depoint ((PT)) (Pointer PT))
(declare-const _v PT)
(declare-const _p (Pointer PT)) 
(assert (iff (= (depoint _v) _p) (= _v (value _p))))

(declare-fun _66_DRB002-antidep1-var-yes_c_t_THREAD1 () Int)
(declare-fun _66_DRB002-antidep1-var-yes_c_chunk_size () Int)
(declare-fun _66_DRB002-antidep1-var-yes_c_t_THREAD2 () Int)
(declare-fun _66_DRB002-antidep1-var-yes_c_chunk_THREAD1 () Int)
(declare-fun i_66_2308_DRB002-antidep1-var-yes_c_FUNCTION () Int)

(declare-fun a_67_2317_DRB002-antidep1-var-yes_c () (Array Int Int))

(declare-fun a_60_DRB002-antidep1-var-yes_c () (Array Int Int))
(assert (= a_67_2317_DRB002-antidep1-var-yes_c a_60_DRB002-antidep1-var-yes_c))
(declare-fun i_66_2308_DRB002-antidep1-var-yes_c_THREAD2 () Int)
(declare-fun i_66_2308_DRB002-antidep1-var-yes_c_THREAD1 () Int)
(declare-fun _66_DRB002-antidep1-var-yes_c_chunk_THREAD2 () Int)

(declare-fun a_67_2322_DRB002-antidep1-var-yes_c () (Array Int Int))

(assert (= a_67_2322_DRB002-antidep1-var-yes_c a_60_DRB002-antidep1-var-yes_c))
(declare-fun len_55_DRB002-antidep1-var-yes_c_CONST () Int)
(declare-fun nthreads_66_DRB002-antidep1-var-yes_c () Int)
(declare-fun atoi (Str) Int)
(define-fun main ((argc_52_DRB002-antidep1-var-yes_c Int)
(argv_52_DRB002-antidep1-var-yes_c (Pointer (Pointer Void)))) Int 0)

(define-fun ParallelCondition () Bool (and 

(and (and (< _66_DRB002-antidep1-var-yes_c_t_THREAD1 nthreads_66_DRB002-antidep1-var-yes_c) (< _66_DRB002-antidep1-var-yes_c_t_THREAD2 nthreads_66_DRB002-antidep1-var-yes_c) (<= 0 _66_DRB002-antidep1-var-yes_c_t_THREAD2) (<= 0 _66_DRB002-antidep1-var-yes_c_t_THREAD1) (not (= _66_DRB002-antidep1-var-yes_c_t_THREAD1 _66_DRB002-antidep1-var-yes_c_t_THREAD2)) (not (= _66_DRB002-antidep1-var-yes_c_chunk_THREAD1 _66_DRB002-antidep1-var-yes_c_chunk_THREAD2)) (< 0 _66_DRB002-antidep1-var-yes_c_t_THREAD1 nthreads_66_DRB002-antidep1-var-yes_c)) (<= 0 _66_DRB002-antidep1-var-yes_c_chunk_THREAD2 MAX_INT) (<= 1 nthreads_66_DRB002-antidep1-var-yes_c MAX_INT) (<= 0 _66_DRB002-antidep1-var-yes_c_t_THREAD1 MAX_INT) (<= 0 _66_DRB002-antidep1-var-yes_c_t_THREAD2 MAX_INT) (<= 0 _66_DRB002-antidep1-var-yes_c_chunk_THREAD1 MAX_INT))
(<= 0 _66_DRB002-antidep1-var-yes_c_chunk_THREAD2 MAX_INT)
(<= 1 nthreads_66_DRB002-antidep1-var-yes_c MAX_INT)
(<= 0 _66_DRB002-antidep1-var-yes_c_t_THREAD1 MAX_INT)
(<= 0 _66_DRB002-antidep1-var-yes_c_t_THREAD2 MAX_INT)
(<= 0 _66_DRB002-antidep1-var-yes_c_chunk_THREAD1 MAX_INT)
))

;_LB,     _1,    _UB
(define-fun InCarryInRange ((_1 Int)(_LB Int)(_UB Int)) Bool (and
  (<= _LB _1)(<= _1 _UB)
))
(define-fun InCarryInRangeUB ((_1 Int)(_UB Int)) Bool (or
  (= _1 _UB)
  (< _1 _UB)
))
(define-fun InCarryInRangeLB ((_1 Int)(_LB Int)) Bool (or
  (= _1 _LB)
  (> _1 _LB)
))

(echo "Range down-grade...")
;RangeDegradeUB(define-fun InRange ((_1 Int)) Bool (InCarryInRangeUB _1 9223372036854775807))
;RangeDegradeIn(define-fun InRange ((_1 Int)) Bool (InCarryInRange _1 0 9223372036854775807))
;RangeDegradeLB(define-fun InRange ((_1 Int)) Bool (InCarryInRangeLB _1 0))
;RangeDegradeParams(assert (InRange nthreads_66_DRB002-antidep1-var-yes_c))


(define-fun RaceCondition () Bool 
(and (= (store a_67_2317_DRB002-antidep1-var-yes_c i_66_2308_DRB002-antidep1-var-yes_c_THREAD1 (+ (select a_67_2322_DRB002-antidep1-var-yes_c (+ i_66_2308_DRB002-antidep1-var-yes_c_THREAD1 1)) 1)) a_67_2317_DRB002-antidep1-var-yes_c) (= i_66_2308_DRB002-antidep1-var-yes_c_THREAD1 (+ i_66_2308_DRB002-antidep1-var-yes_c_THREAD2 1)) (= (store a_67_2317_DRB002-antidep1-var-yes_c i_66_2308_DRB002-antidep1-var-yes_c_THREAD2 (+ (select a_67_2322_DRB002-antidep1-var-yes_c (+ i_66_2308_DRB002-antidep1-var-yes_c_THREAD2 1)) 1)) a_67_2317_DRB002-antidep1-var-yes_c))
)



(assert RaceCondition)
(assert ParallelCondition)

(assert (= (store a_67_2317_DRB002-antidep1-var-yes_c i_66_2308_DRB002-antidep1-var-yes_c_THREAD1 (+ (select a_67_2322_DRB002-antidep1-var-yes_c (+ i_66_2308_DRB002-antidep1-var-yes_c_THREAD1 1)) 1)) a_67_2317_DRB002-antidep1-var-yes_c))
(assert (= (store a_67_2317_DRB002-antidep1-var-yes_c i_66_2308_DRB002-antidep1-var-yes_c_THREAD1 (+ (select a_67_2322_DRB002-antidep1-var-yes_c (+ i_66_2308_DRB002-antidep1-var-yes_c_THREAD1 1)) 1)) a_67_2317_DRB002-antidep1-var-yes_c))
(assert (= i_66_2308_DRB002-antidep1-var-yes_c_THREAD1 (+ i_66_2308_DRB002-antidep1-var-yes_c_THREAD2 1)))
(assert (<= MIN_INT _66_DRB002-antidep1-var-yes_c_t_THREAD1 MAX_INT))
(assert (= (store a_67_2317_DRB002-antidep1-var-yes_c i_66_2308_DRB002-antidep1-var-yes_c_THREAD2 (+ (select a_67_2322_DRB002-antidep1-var-yes_c (+ i_66_2308_DRB002-antidep1-var-yes_c_THREAD2 1)) 1)) a_67_2317_DRB002-antidep1-var-yes_c))
(assert (<= 0 i_66_2308_DRB002-antidep1-var-yes_c_THREAD2 (ite (< 0 (- len_55_DRB002-antidep1-var-yes_c_CONST 1)) (- (- len_55_DRB002-antidep1-var-yes_c_CONST 1) 1) 0)))
(assert (<= 0 i_66_2308_DRB002-antidep1-var-yes_c_THREAD1 (ite (< 0 (- len_55_DRB002-antidep1-var-yes_c_CONST 1)) (- (- len_55_DRB002-antidep1-var-yes_c_CONST 1) 1) 0)))

(check-sat)
(get-model)
(exit)