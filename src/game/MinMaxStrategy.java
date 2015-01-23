package game;

public class MinMaxStrategy implements Strategy {
	public static final String NAME = "MiniMax";

	private Disc disc;
	private int maxDepth;

	public MinMaxStrategy(int maxDepth) {
		this.maxDepth = maxDepth;
	}

	public String getName() {
		return NAME;
	}

	public int determineMove(Board b, Disc d) {
		this.disc = d;
		int c = -1;
		int score = Integer.MIN_VALUE;
		for (int col = 0; col < b.getColumns(); col++) {
			if (b.isEmptyField(col)) {
				int row = b.emptyRow(col);
				b.setField(row, col, d);
				if (b.isWinner(d)) {
					return col;
				}
				b.setField(row, col, d.other());
				if (b.isWinner(d.other())) {
					return col;
				}
				b.setField(row, col, d);
				int newScore = evaluateMove(b, 1, disc);
				b.setField(row, col, Disc.EMPTY);
				if (newScore > score) {
					score = newScore;
					c = col;
				}
			}
		}
		return c;
	}

	private int evaluateMove(Board b, int depth, Disc d) {
		if (b.isWinner(d)) {
			if (d == disc) {
				return twoPow(maxDepth - depth);
			} else {
				return -twoPow(maxDepth - depth);
			}
		} else if (depth == maxDepth) {
			return 0;
		}
		int score = 0;
		for (int col = 0; col < b.getColumns(); col++) {
			if (b.isEmptyField(col)) {
				int row = b.emptyRow(col);
				b.setField(row, col, d.other());
				score += evaluateMove(b, depth + 1, d.other());
				b.setField(row, col, Disc.EMPTY);
			}
		}
		return score;
	}

	private int twoPow(int exp) {
		int result = 1;
		for (int i = 0; i < exp; i++) {
			result *= 2;
		}
		return result;
	}

	private int fieldsLeft(Board b) {
		int fields = 0;
		for (int row = 0; row < b.getRows(); row++) {
			for (int col = 0; col < b.getColumns(); col++) {
				if (b.getField(row, col) == Disc.EMPTY) {
					fields++;
				}
			}
		}
		return fields;
	}

	public static void main(String[] args) {
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
		MinMaxStrategy minimax = new MinMaxStrategy(8);
		Disc d = Disc.RED;
		int col = minimax.determineMove(board, d);
		System.out.println("Place in column: " + col);
		board.insertDisc(col, d);
		System.out.println(board);

	}

}
