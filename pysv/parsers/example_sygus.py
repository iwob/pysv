from pysv.parsers import sygus


spec1 = """
(set-logic LIA)

;; rec(x,y,z) \equiv (* (+ x x) (- y z))

(synth-fun rec ((x Int) (y Int) (z Int)) Int
       (
       (Start Int (x
                   y
                  z
               (* Start Start)
               (+ Start Start)
               (- Start Start)
       ))))

(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)

(constraint (= (rec x1 x2 x3) (* (+ x1 x1) (- x2 x3))))

(check-synth)
"""

ast = sygus.parse(spec1)
print("AST tree of spec1:\n" + str(ast))


spec2 = """
(set-logic LIA)
(synth-fun findIdx ( (y1 Int) (y2 Int) (k1 Int)) Int (
(Start Int ( 0 1 2 y1 y2 k1 (ite BoolExpr Start Start)))
(BoolExpr Bool ((< Start Start) (<= Start Start) (> Start Start) (>= Start Start)))))

(declare-var x1 Int)
(declare-var x2 Int)
(declare-var k (BitVec 8))
(constraint (=> (< x1 x2) (=> (< k x1) (= (findIdx x1 x2 k) 0))))
(constraint (=> (< x1 x2) (=> (> k x2) (= (findIdx x1 x2 k) 2))))
(constraint (=> (< x1 x2) (=> (and (> k x1) (< k x2)) (= (findIdx x1 x2 k) 1))))
(check-synth)
"""

ast = sygus.parse(spec2)
print("\nAST tree of spec2:\n" + str(ast))