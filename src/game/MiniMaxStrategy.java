package game;

//TODO: Als alle zetten even goed zijn, dan zoveel mogelijk in het midden gooien.
public class MiniMaxStrategy implements Strategy {
	public static final String NAME = "MiniMax";

	private Disc disc;
	private int maxDepth;

	public MiniMaxStrategy(int maxDepth) {
		this.maxDepth = maxDepth;
	}

	@Override
	public String getName() {
		return NAME;
	}

	@Override
	public int determineMove(Board b, Disc d) {
		this.disc = d;
		int c = -1;
		int score = Integer.MIN_VALUE;
		for (int col = 0; col < b.getColumns(); col++) {
			if (b.isEmptyField(col)) {
				int row = b.emptyRow(col);
				int newScore = evaluateMove(b, row, col, 1, disc);
				b.setField(row, col, Disc.EMPTY);
				if (newScore > score) {
					score = newScore;
					c = col;
				}
			}
		}
		return c;
	}

	private int evaluateMove(Board b, int row, int col, int depth, Disc d) {
		b.setField(row, col, d);
		if (b.isWinner(d)) {
			if (d == disc) {
				return twoPow(maxDepth - depth);
			} else {
				return -twoPow(maxDepth - depth);
			}
		}
		b.setField(row, col, d.other());
		if (b.isWinner(d.other())) {
			if (d == disc) {
				return twoPow(maxDepth - depth);
			} else {
				return -twoPow(maxDepth - depth);
			}
		}
		if (depth == maxDepth) {
			return 0;
		}
		b.setField(row, col, d);
		int score = 0;
		for (int c = 0; c < b.getColumns(); c++) {
			if (b.isEmptyField(c)) {
				int r = b.emptyRow(c);
				score += evaluateMove(b, r, c, depth + 1, d.other());
				b.setField(r, c, Disc.EMPTY);
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
		MiniMaxStrategy minimax = new MiniMaxStrategy(8);
		Disc d = Disc.RED;
		int col = minimax.determineMove(board, d);
		System.out.println("Place in column: " + col);
		board.insertDisc(col, d);
		System.out.println(board);

	}

}
