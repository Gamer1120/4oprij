package game;

import java.util.HashMap;
import java.util.LinkedList;

public class PerfectStrategy extends Thread implements Strategy {
	public final static String NAME = "Perfect";
	public final static int DEPTH = 3;
	private Board board;
	private Disc disc;
	private HashMap<Integer, Integer> scores;

	public PerfectStrategy(Board b, Disc d, int currDepth) {
		this.board = b;
		this.disc = d;
	}

	@Override
	public int determineMove(Board b, Disc d) {
		// Start depth = 0
		new PerfectStrategy(b, d, 0);
		return 0;
	}

	public void run() {
		// First create a copy of the board
		Board copy = board.deepCopy();
		// Now check if there's an insta-win available
		LinkedList<Integer> canWin = instantWin(copy, disc);
		// In case there is:
		if (canWin != null) {
			// For all direct wins: Set the score to 1000.
			for (Integer col : canWin) {
				scores.put(col, 1000);
			}
		}
		// Now check for the opponent: if you make a certain move, can he win?
		if (disc == Disc.RED) {
			// Check for all columns
			for (int col = 0; col < board.getColumns(); col++) {
				// Make a copy of the board
				copy = board.deepCopy();
				// Insert a disc into that column
				copy.insertDisc(col, Disc.RED);
				// Check if it's possible to win for the opponent
				canWin = instantWin(copy, Disc.YELLOW);
				// If it's possible to win for the opponent
				if (canWin != null) {
					if (scores.get(col) != 1000) {
						scores.put(col, -1000);
					}

				}
			}

		} else if (disc == Disc.YELLOW) {
			// Check for all columns
			for (int col = 0; col < board.getColumns(); col++) {
				// Make a copy of the board
				copy = board.deepCopy();
				// Insert a disc into that column
				copy.insertDisc(col, Disc.YELLOW);
				// Check if it's possible to win for the opponent
				canWin = instantWin(copy, Disc.RED);
				// If it's possible to win for the opponent
				if (canWin != null) {
					if (scores.get(col) != 1000) {
						scores.put(col, -1000);
					}

				}
			}
		}
	}

	private LinkedList<Integer> instantWin(Board b, Disc d) {
		LinkedList<Integer> winColumns = null;
		for (int col = 0; col < board.getColumns(); col++) {
			Board copy = b.deepCopy();
			copy.insertDisc(col, d);
			if (copy.hasWinner()) {
				winColumns.add(col);
			}
		}
		return winColumns;
	}

	public static void main(String[] args) {
		new PerfectStrategy(new Board(), Disc.RED, 9).start();
	}
}