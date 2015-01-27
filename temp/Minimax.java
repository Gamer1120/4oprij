package temp;

import game.Board;
import game.Disc;

public class Minimax {
	private final Board board;
	public static final int[] INCREMENT = { 0, 1, 4, 32, 128, 512 };
	private int column, maxDepth;

	public Minimax(Board board, int maxDepth) {
		this.board = board;
		this.maxDepth = maxDepth;
	}

	public int alphaBeta(Disc d) {
		if (d == Disc.YELLOW) {
			evaluateYellowMove(0, maxDepth, -1, Integer.MIN_VALUE + 1,
					Integer.MAX_VALUE - 1);
		} else {
			evaluateRedMove(0, maxDepth, -1, Integer.MIN_VALUE + 1,
					Integer.MAX_VALUE - 1);
		}
		return column;
	}

	private int evaluateRedMove(int depth, int maxDepth, int col, int alpha,
			int beta) {
		int min = Integer.MAX_VALUE, score = 0;
		if (col != -1) {
			score = getHeuristicScore(Disc.YELLOW, board, col, depth, maxDepth);
			if (board.isWinner(Disc.YELLOW)) {
				return score;
			}
		}
		if (depth == maxDepth) {
			return score;
		}
		for (int c = 0; c < board.getColumns(); c++) {
			//TODO: werken met deepcopy inplaats van disc verwijderen?
			if (board.isEmptyField(c)) {
				int r = board.emptyRow(c);
				board.setField(r, c, Disc.RED);
				int value = evaluateYellowMove(depth + 1, maxDepth, c, alpha,
						beta);
				board.setField(r, c, Disc.EMPTY);
				if (value < min) {
					min = value;
					if (depth == 0) {
						column = c;
					}
				}
				if (value < beta) {
					beta = value;
				}
				if (alpha >= beta) {
					return beta;
				}
			}
		}

		if (min == Integer.MAX_VALUE) {
			return 0;
		}
		return min;
	}

	private int evaluateYellowMove(int depth, int maxDepth, int col, int alpha,
			int beta) {
		int max = Integer.MIN_VALUE, score = 0;
		if (col != -1) {
			score = getHeuristicScore(Disc.RED, board, col, depth, maxDepth);
			if (board.isWinner(Disc.RED)) {
				return score;
			}
		}
		if (depth == maxDepth) {
			return score;
		}
		for (int c = 0; c < board.getColumns(); c++) {
			if (board.isEmptyField(c)) {
				int r = board.emptyRow(c);
				board.setField(r, c, Disc.YELLOW);
				int value = evaluateRedMove(depth + 1, maxDepth, c, alpha, beta);
				board.setField(r, c, Disc.EMPTY);
				if (value > max) {
					max = value;
					if (depth == 0) {
						column = c;
					}
				}
				if (value > alpha) {
					alpha = value;
				}
				if (alpha >= beta) {
					return alpha;
				}
			}
		}
		if (max == Integer.MIN_VALUE) {
			return 0;
		}
		return max;
	}

	public int getHeuristicScore(Disc d, Board board, int col, int depth,
			int maxDepth) {
		int score = 0, row = board.emptyRow(col) + 1, redCount, yellowCount;

		redCount = yellowCount = 0;
		int cStart = col - 3, colStart = cStart >= 0 ? cStart : 0, colEnd = board
				.getColumns() - 3 - (colStart - cStart);
		for (int c = colStart; c < colEnd; c++) {
			redCount = yellowCount = 0;
			for (int val = 0; val < 4; val++) {
				Disc disc = board.getField(row, c + val);
				if (disc == Disc.RED) {
					redCount++;
				} else if (disc == Disc.YELLOW) {
					yellowCount++;
				}
			}
			if (redCount == 4) {
				if (depth <= 2) {
					return Integer.MIN_VALUE + 1;
				}
			} else if (yellowCount == 4) {
				if (depth <= 2) {
					return Integer.MAX_VALUE - 1;
				}
			}
			score += getScoreIncrement(redCount, yellowCount, d);
		}

		redCount = yellowCount = 0;
		int rowEnd = Math.min(board.getRows(), row + 4);
		for (int r = row; r < rowEnd; r++) {
			Disc disc = board.getField(r, col);
			if (disc == Disc.RED) {
				redCount++;
			} else if (disc == Disc.YELLOW) {
				yellowCount++;
			}
		}
		if (redCount == 4) {
			if (depth <= 2) {
				return Integer.MIN_VALUE + 1;
			}
		} else if (yellowCount == 4) {
			if (depth <= 2) {
				return Integer.MAX_VALUE - 1;
			}
		}
		score += getScoreIncrement(redCount, yellowCount, d);

		int minValue = Math.min(row, col), rowStart = row - minValue;
		colStart = col - minValue;
		for (int r = rowStart, c = colStart; r <= board.getRows() - 4
				&& c <= board.getColumns() - 4; r++, c++) {
			redCount = yellowCount = 0;
			for (int val = 0; val < 4; val++) {
				Disc disc = board.getField(r + val, c + val);
				if (disc == Disc.RED) {
					redCount++;
				} else if (disc == Disc.YELLOW) {
					yellowCount++;
				}
			}
			if (redCount == 4) {
				if (depth <= 2) {
					return Integer.MIN_VALUE + 1;
				}
			} else if (yellowCount == 4) {
				if (depth <= 2) {
					return Integer.MAX_VALUE - 1;
				}
			}
			score += getScoreIncrement(redCount, yellowCount, d);
		}

		minValue = Math.min(board.getRows() - 1 - row, col);
		rowStart = row + minValue;
		colStart = col - minValue;
		for (int r = rowStart, c = colStart; r >= 3
				&& c <= board.getColumns() - 4; r--, c++) {
			redCount = yellowCount = 0;
			for (int val = 0; val < 4; val++) {
				Disc disc = board.getField(r - val, c + val);
				if (disc == Disc.RED) {
					redCount++;
				} else if (disc == Disc.YELLOW) {
					yellowCount++;
				}
			}
			if (redCount == 4) {
				if (depth <= 2) {
					return Integer.MIN_VALUE + 1;
				}
			} else if (yellowCount == 4) {
				if (depth <= 2) {
					return Integer.MAX_VALUE - 1;
				}
			}
			score += getScoreIncrement(redCount, yellowCount, d);
		}
		return score;
	}

	private int getScoreIncrement(int redCount, int yellowCount, Disc d) {
		if (redCount == yellowCount) {
			if (d == Disc.RED) {
				return -1;
			}
			return 1;
		} else if (redCount < yellowCount) {
			if (d == Disc.RED) {
				return INCREMENT[yellowCount] - INCREMENT[redCount];
			}
			return INCREMENT[yellowCount + 1] - INCREMENT[redCount];
		} else {
			if (d == Disc.RED) {
				return -INCREMENT[redCount + 1] + INCREMENT[yellowCount];
			}
			return -INCREMENT[redCount] + INCREMENT[yellowCount];
		}
	}

	public static void main(String[] args) {
		// This section is for testing purposes only, in cases where the
		// computer makes a seemingly bad choice.
		Board board = new Board();
		board.insertDisc(0, Disc.RED);
		board.insertDisc(0, Disc.RED);

		board.insertDisc(1, Disc.YELLOW);
		board.insertDisc(1, Disc.RED);
		board.insertDisc(1, Disc.YELLOW);
		board.insertDisc(1, Disc.YELLOW);
		board.insertDisc(1, Disc.RED);
		board.insertDisc(1, Disc.RED);

		board.insertDisc(2, Disc.RED);
		board.insertDisc(2, Disc.RED);
		board.insertDisc(2, Disc.RED);
		board.insertDisc(2, Disc.YELLOW);
		board.insertDisc(2, Disc.RED);

		board.insertDisc(3, Disc.RED);
		board.insertDisc(3, Disc.YELLOW);
		board.insertDisc(3, Disc.RED);
		board.insertDisc(3, Disc.YELLOW);
		board.insertDisc(3, Disc.YELLOW);
		board.insertDisc(3, Disc.YELLOW);

		board.insertDisc(4, Disc.YELLOW);
		board.insertDisc(4, Disc.RED);
		board.insertDisc(4, Disc.YELLOW);
		board.insertDisc(4, Disc.RED);

		board.insertDisc(6, Disc.YELLOW);
		board.insertDisc(6, Disc.YELLOW);
		board.insertDisc(6, Disc.YELLOW);
		board.insertDisc(6, Disc.RED);
		board.insertDisc(6, Disc.YELLOW);

		System.out.println(board);
		Minimax minimax = new Minimax(board, 8);
		Disc d = Disc.RED;
		int col = minimax.alphaBeta(d);
		System.out.println("Place in column: " + col);
		board.insertDisc(col, d);
		System.out.println(board);
	}
}
