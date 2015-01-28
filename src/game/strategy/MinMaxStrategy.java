package game.strategy;

import game.Board;
import game.Disc;

/**
 * client program for the Connect4 according to the protocol of the TI-2 group.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */

public class MinMaxStrategy implements Strategy {
	/**
	 * The name of this Strategy.
	 */
	public static final String NAME = "MiniMax";
	/**
	 * The amount of multiplication used for calculating the score, if pow is 2
	 * than the score of a win on a depth of 3 will be twice the score of a win
	 * on depth 4.
	 */
	public final static int BASE = 8;
	/**
	 * The Disc this MinMaxStrategy uses.
	 */
	private Disc disc;

	/**
	 * The amount of turns this MinMaxStrategy thinks ahead.
	 */
	private int maxDepth;

	/*@	private invariant disc == Disc.YELLOW || disc == Disc.RED;
	 	private invariant maxDepth > 0;
	 */

	/**
	 * Creates a new MinMaxStrategy with a depth of 4.
	 */
	public MinMaxStrategy() {
		this(8);
	}

	/**
	 * Creates a new MinMaxStrategy with the specified depth.
	 * 
	 * @param maxDepth
	 *            The depth this MinMaxStrategy will use.
	 */
	//@ requires maxDepth > 0;
	//@ ensures getDepth() == maxDepth;
	public MinMaxStrategy(int maxDepth) {
		this.maxDepth = maxDepth;
	}

	/**
	 * Returns the name of this MinMaxStrategy.
	 * 
	 * @return The name of this MinMaxStrategy.
	 */
	@Override
	/*@ pure */public String getName() {
		return NAME;
	}

	/**
	 * Returns the depth of this MinMaxStrategy.
	 * 
	 * @return The depth of this MinMaxStrategy.
	 */
	/*@ pure */public int getDepth() {
		return maxDepth;
	}

	/**
	 * Sets the depth for this MinMaxStrategy.
	 * 
	 * @param maxDepth
	 *            The depth to set for this MinMaxStrategy.
	 */
	//@ requires maxDepth > 0;
	//@ ensures getDepth() == maxDepth;
	public void setDepth(int maxDepth) {
		this.maxDepth = maxDepth;
	}

	/**
	 * Determines a move according to the MinMax algorithm.
	 * 
	 * @param b
	 *            The Board to determine a move for.
	 * @param d
	 *            The Disc to determine the move for.
	 */
	//@ requires b != null;
	//@ requires d == Disc.YELLOW || d == Disc.RED;
	@Override
	public int determineMove(Board b, Disc d) {
		this.disc = d;
		int c = -1;
		int score = Integer.MIN_VALUE;
		/*@ loop_invariant 0 <= col && col <= b.getColumns();
			loop_invariant b.isField(col);
		 */
		for (int col = 0; col < b.getColumns(); col++) {
			if (b.isEmptyField(col)) {
				int row = b.emptyRow(col);
				b.setField(row, col, d);
				if (b.isWinner(d)) {
					b.setField(row, col, Disc.EMPTY);
					return col;
				}
				b.setField(row, col, d.other());
				if (b.isWinner(d.other())) {
					b.setField(row, col, Disc.EMPTY);
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

	/**
	 * Gives a score to a move. The higher the score, the better the move is.
	 * 
	 * @param b
	 *            The board to determine a move for.
	 * @param depth
	 *            The maximum search depth.
	 * @param d
	 *            The Disc to determine a score for.
	 * @return The score for this move.
	 */
	private int evaluateMove(Board b, int depth, Disc d) {
		if (b.isWinner(d)) {
			if (d == disc) {
				return pow(maxDepth - depth);
			} else {
				return -pow(maxDepth - depth);
			}
			/*
			 * Shouldn't be larger, except when the user changes the
			 * thinking time while the computer is thinking.
			 */
		} else if (depth >= maxDepth) {
			return 0;
		}
		int score = 0;
		/*@ loop_invariant 0 <= col && col <= b.getColumns();
			loop_invariant b.isField(col);
		*/
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

	/**
	 * This method calculates BASE^exp. This is used to calculate the score.
	 * 
	 * @param exp
	 *            The exponent.
	 * @return BASE^exp.
	 */
	/*@ requires exp >= 0;
		requires BASE >= 0;
		ensures \result == Math.pow(BASE, exp);
	 */
	private int pow(int exp) {
		int result = 1;
		//@ loop_invariant 0 <= i && i <= exp;
		for (int i = 0; i < exp; i++) {
			result *= BASE;
		}
		return result;
	}
}
