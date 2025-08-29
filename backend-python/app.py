from flask import Flask, request, jsonify
from solver import solve_puzzle

app = Flask(__name__)

# ---- CORS support ----
from flask_cors import CORS
CORS(app)
# ----------------------

@app.route('/solve-puzzle', methods=['POST'])
def solve():
    try:
        data = request.get_json()
        board = data.get('board')
        size = data.get('size')
        if not board or not size:
            return jsonify({'error': 'Missing board or size'}), 400
        solution = solve_puzzle(board, size)
        if not solution:
            return jsonify({'solution': None, 'error': 'No solution found'}), 200
        return jsonify({'solution': solution}), 200
    except Exception as e:
        return jsonify({'error': str(e)}), 500

if __name__ == "__main__":
    app.run(debug=True)
