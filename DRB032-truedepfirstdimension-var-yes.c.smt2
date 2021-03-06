

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
(declare-fun pt2i ((Pointer PT)) Int)
(declare-fun i2pt (Int) (Pointer PT))
(declare-fun r2pt (Real) (Pointer PT))
(declare-fun b2pt (Bool) (Pointer PT))
(define-fun point ((_p (Pointer PT))) (Pointer PT)
				  (ite (is-ptr _p) (addr _p) _p) 
) 
(declare-fun depoint (PT) (Pointer PT))
(declare-const _v PT)
(declare-const _p (Pointer PT))
(assert (iff (= (depoint _v) _p) (= _v (value _p))))

(declare-fun j_THREAD1_2_68_2408_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun j_THREAD1_68_2408_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun i_null_null_null_FUNCTION_69_2421_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun b_null_null_null_null_FUNCTION_69_2419_DRB032-truedepfirstdimension-var-yes_c (Int Int Int Int ) Real)
(declare-fun _chunk_67_DRB032-truedepfirstdimension-var-yes_c_THREAD2__chunk_67_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun j_THREAD1_2_69_2434_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun m_59_DRB032-truedepfirstdimension-var-yes_c_59_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun j_THREAD2_69_2424_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun j_null_FUNCTION_68_2408_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun j_FUNCTION_69_2434_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun j_THREAD1_2_69_2424_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun _t_67_DRB032-truedepfirstdimension-var-yes_c_THREAD1__t_67_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun j_THREAD1_1_69_2434_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun _t_67_DRB032-truedepfirstdimension-var-yes_c_FUNCTION__t_67_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun j_THREAD1_1_69_2424_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun j_FUNCTION_69_2424_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun _t_67_DRB032-truedepfirstdimension-var-yes_c_THREAD2__t_67_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun i_null_null_null_FUNCTION_69_2429_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun j_THREAD2_68_2408_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun j_THREAD1_1_68_2408_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun j_THREAD2_69_2434_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun _chunk_67_DRB032-truedepfirstdimension-var-yes_c_THREAD1__chunk_67_DRB032-truedepfirstdimension-var-yes_c () Int)
(declare-fun _nthreads__nthreads () Int)		;RangeDegradeParam
(declare-fun _chunk_size_67_DRB032-truedepfirstdimension-var-yes_c__chunk_size_67_DRB032-truedepfirstdimension-var-yes_c () Int)
(define-fun main_Int_pt_Str ((argc_52_DRB032-truedepfirstdimension-var-yes_c_52_DRB032-truedepfirstdimension-var-yes_c Int)(argv_52_DRB032-truedepfirstdimension-var-yes_c (Pointer PT))) Int 0)
(declare-fun atoi (Str) Int)
(declare-fun b_null_null_null_null_FUNCTION_69_2419_DRB032-truedepfirstdimension-var-yes_c_Int_Int_Int_Int (Int Int Int Int ) Real)

(define-fun ParallelCondition () Bool (and 

(and (and (not (= _t_67_DRB032-truedepfirstdimension-var-yes_c_THREAD1__t_67_DRB032-truedepfirstdimension-var-yes_c _t_67_DRB032-truedepfirstdimension-var-yes_c_THREAD2__t_67_DRB032-truedepfirstdimension-var-yes_c)) (not (= _chunk_67_DRB032-truedepfirstdimension-var-yes_c_THREAD1__chunk_67_DRB032-truedepfirstdimension-var-yes_c _chunk_67_DRB032-truedepfirstdimension-var-yes_c_THREAD2__chunk_67_DRB032-truedepfirstdimension-var-yes_c)) (<= 0 _t_67_DRB032-truedepfirstdimension-var-yes_c_THREAD1__t_67_DRB032-truedepfirstdimension-var-yes_c) (<= 0 _t_67_DRB032-truedepfirstdimension-var-yes_c_THREAD2__t_67_DRB032-truedepfirstdimension-var-yes_c) (< _t_67_DRB032-truedepfirstdimension-var-yes_c_THREAD2__t_67_DRB032-truedepfirstdimension-var-yes_c _nthreads__nthreads) (< _t_67_DRB032-truedepfirstdimension-var-yes_c_THREAD1__t_67_DRB032-truedepfirstdimension-var-yes_c _nthreads__nthreads) (< 0 _t_67_DRB032-truedepfirstdimension-var-yes_c_FUNCTION__t_67_DRB032-truedepfirstdimension-var-yes_c _nthreads__nthreads)) (<= 0 _t_67_DRB032-truedepfirstdimension-var-yes_c_FUNCTION__t_67_DRB032-truedepfirstdimension-var-yes_c MAX_INT) (<= 0 _chunk_67_DRB032-truedepfirstdimension-var-yes_c_THREAD2__chunk_67_DRB032-truedepfirstdimension-var-yes_c MAX_INT) (<= 0 _t_67_DRB032-truedepfirstdimension-var-yes_c_THREAD2__t_67_DRB032-truedepfirstdimension-var-yes_c MAX_INT) (<= 0 _chunk_67_DRB032-truedepfirstdimension-var-yes_c_THREAD1__chunk_67_DRB032-truedepfirstdimension-var-yes_c MAX_INT) (<= 1 _nthreads__nthreads MAX_INT) (<= 0 _t_67_DRB032-truedepfirstdimension-var-yes_c_THREAD1__t_67_DRB032-truedepfirstdimension-var-yes_c MAX_INT))
(<= 0 _t_67_DRB032-truedepfirstdimension-var-yes_c_FUNCTION__t_67_DRB032-truedepfirstdimension-var-yes_c MAX_INT)
(<= 0 _chunk_67_DRB032-truedepfirstdimension-var-yes_c_THREAD2__chunk_67_DRB032-truedepfirstdimension-var-yes_c MAX_INT)
(<= 0 _t_67_DRB032-truedepfirstdimension-var-yes_c_THREAD2__t_67_DRB032-truedepfirstdimension-var-yes_c MAX_INT)
(<= 0 _chunk_67_DRB032-truedepfirstdimension-var-yes_c_THREAD1__chunk_67_DRB032-truedepfirstdimension-var-yes_c MAX_INT)
(<= 1 _nthreads__nthreads MAX_INT)
(<= 0 _t_67_DRB032-truedepfirstdimension-var-yes_c_THREAD1__t_67_DRB032-truedepfirstdimension-var-yes_c MAX_INT)
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
;RangeDegradeParams(assert (InRange _nthreads__nthreads))


(define-fun RaceCondition () Bool 

(and (= (b_null_null_null_null_FUNCTION_69_2419_DRB032-truedepfirstdimension-var-yes_c i_null_null_null_FUNCTION_69_2421_DRB032-truedepfirstdimension-var-yes_c j_THREAD1_1_69_2424_DRB032-truedepfirstdimension-var-yes_c j_THREAD1_1_69_2424_DRB032-truedepfirstdimension-var-yes_c j_THREAD1_1_69_2424_DRB032-truedepfirstdimension-var-yes_c) (b_null_null_null_null_FUNCTION_69_2419_DRB032-truedepfirstdimension-var-yes_c (- i_null_null_null_FUNCTION_69_2429_DRB032-truedepfirstdimension-var-yes_c 1) (- j_THREAD1_1_69_2434_DRB032-truedepfirstdimension-var-yes_c 1) (- j_THREAD1_1_69_2434_DRB032-truedepfirstdimension-var-yes_c 1) (- j_THREAD1_1_69_2434_DRB032-truedepfirstdimension-var-yes_c 1))) (= (b_null_null_null_null_FUNCTION_69_2419_DRB032-truedepfirstdimension-var-yes_c i_null_null_null_FUNCTION_69_2421_DRB032-truedepfirstdimension-var-yes_c j_THREAD1_1_69_2424_DRB032-truedepfirstdimension-var-yes_c j_THREAD1_1_69_2424_DRB032-truedepfirstdimension-var-yes_c j_THREAD1_1_69_2424_DRB032-truedepfirstdimension-var-yes_c) (b_null_null_null_null_FUNCTION_69_2419_DRB032-truedepfirstdimension-var-yes_c (- i_null_null_null_FUNCTION_69_2429_DRB032-truedepfirstdimension-var-yes_c 1) (- j_THREAD1_1_69_2434_DRB032-truedepfirstdimension-var-yes_c 1) (- j_THREAD1_1_69_2434_DRB032-truedepfirstdimension-var-yes_c 1) (- j_THREAD1_1_69_2434_DRB032-truedepfirstdimension-var-yes_c 1))) (= (b_null_null_null_null_FUNCTION_69_2419_DRB032-truedepfirstdimension-var-yes_c i_null_null_null_FUNCTION_69_2421_DRB032-truedepfirstdimension-var-yes_c j_THREAD1_1_69_2424_DRB032-truedepfirstdimension-var-yes_c j_THREAD1_1_69_2424_DRB032-truedepfirstdimension-var-yes_c j_THREAD1_1_69_2424_DRB032-truedepfirstdimension-var-yes_c) (b_null_null_null_null_FUNCTION_69_2419_DRB032-truedepfirstdimension-var-yes_c (- i_null_null_null_FUNCTION_69_2429_DRB032-truedepfirstdimension-var-yes_c 1) (- j_THREAD1_1_69_2434_DRB032-truedepfirstdimension-var-yes_c 1) (- j_THREAD1_1_69_2434_DRB032-truedepfirstdimension-var-yes_c 1) (- j_THREAD1_1_69_2434_DRB032-truedepfirstdimension-var-yes_c 1))) (= j_THREAD1_1_68_2408_DRB032-truedepfirstdimension-var-yes_c j_THREAD1_2_68_2408_DRB032-truedepfirstdimension-var-yes_c) (not (= (b_null_null_null_null_FUNCTION_69_2419_DRB032-truedepfirstdimension-var-yes_c i_null_null_null_FUNCTION_69_2421_DRB032-truedepfirstdimension-var-yes_c j_THREAD1_1_69_2424_DRB032-truedepfirstdimension-var-yes_c j_THREAD1_1_69_2424_DRB032-truedepfirstdimension-var-yes_c j_THREAD1_1_69_2424_DRB032-truedepfirstdimension-var-yes_c) (b_null_null_null_null_FUNCTION_69_2419_DRB032-truedepfirstdimension-var-yes_c i_null_null_null_FUNCTION_69_2421_DRB032-truedepfirstdimension-var-yes_c j_THREAD1_2_69_2424_DRB032-truedepfirstdimension-var-yes_c j_THREAD1_2_69_2424_DRB032-truedepfirstdimension-var-yes_c j_THREAD1_2_69_2424_DRB032-truedepfirstdimension-var-yes_c))))
)



(assert RaceCondition)
(assert ParallelCondition)

(assert (= (b_null_null_null_null_FUNCTION_69_2419_DRB032-truedepfirstdimension-var-yes_c i_null_null_null_FUNCTION_69_2421_DRB032-truedepfirstdimension-var-yes_c j_THREAD1_1_69_2424_DRB032-truedepfirstdimension-var-yes_c j_THREAD1_1_69_2424_DRB032-truedepfirstdimension-var-yes_c j_THREAD1_1_69_2424_DRB032-truedepfirstdimension-var-yes_c) (b_null_null_null_null_FUNCTION_69_2419_DRB032-truedepfirstdimension-var-yes_c (- i_null_null_null_FUNCTION_69_2429_DRB032-truedepfirstdimension-var-yes_c 1) (- j_THREAD1_1_69_2434_DRB032-truedepfirstdimension-var-yes_c 1) (- j_THREAD1_1_69_2434_DRB032-truedepfirstdimension-var-yes_c 1) (- j_THREAD1_1_69_2434_DRB032-truedepfirstdimension-var-yes_c 1))))
(assert (<= 1 j_THREAD2_68_2408_DRB032-truedepfirstdimension-var-yes_c (ite (< 1 m_59_DRB032-truedepfirstdimension-var-yes_c_59_DRB032-truedepfirstdimension-var-yes_c) (- m_59_DRB032-truedepfirstdimension-var-yes_c_59_DRB032-truedepfirstdimension-var-yes_c 1) 1)))
(assert (<= 1 j_THREAD1_68_2408_DRB032-truedepfirstdimension-var-yes_c (ite (< 1 m_59_DRB032-truedepfirstdimension-var-yes_c_59_DRB032-truedepfirstdimension-var-yes_c) (- m_59_DRB032-truedepfirstdimension-var-yes_c_59_DRB032-truedepfirstdimension-var-yes_c 1) 1)))
(assert (<= 1 j_THREAD2_68_2408_DRB032-truedepfirstdimension-var-yes_c (ite (< 1 m_59_DRB032-truedepfirstdimension-var-yes_c_59_DRB032-truedepfirstdimension-var-yes_c) (- m_59_DRB032-truedepfirstdimension-var-yes_c_59_DRB032-truedepfirstdimension-var-yes_c 1) 1)))

(check-sat)
(get-model)
(exit)