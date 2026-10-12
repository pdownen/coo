echo "Building..."
echo "----------------------------------------"
cabal build
echo "========================================"
echo "Testing the evaluator:"
echo "----------------------------------------"
cabal run coo -- test/case/hello.coo
