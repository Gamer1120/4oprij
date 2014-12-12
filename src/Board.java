import java.util.Arrays;

/**
 * Board for the connect4 game.
 * 
 * @author Sven Konings en Michael Koopman
 * @version $Revision: 1.0 $
 */
public class Board {

	// Constants:
	public static final int VERTICAL = 6;
	public static final int HORIZONTAL = 7;
	public static final int ROW = 4;

	// Instance variables
	/*
	 * @ private invariant fields.length == VERTICAL*HORIZONTAL; invariant
	 * (\forall int i; 0 <= i & i < VERTICAL*HORIZONTAL; getField(i) ==
	 * Disc.EMPTY || getField(i) == Disc.YELLOW || getField(i) == Disc.RED);
	 */
	/**
	 * The VERTICAL by HORIZONTAL board of the connect4 game.
	 */
	private Disc[][] fields;

	// Constructors
	/*
	 * @ ensures (\forall int i; 0 <= i & i < VERTICAL; \forall int j; 0 <= j &
	 * j < HORIZONTAL; this.getField(i, j) == Disc.EMPTY);
	 */
	/**
	 * Creates an empty board.
	 */
	public Board() {
		fields = new Disc[VERTICAL][HORIZONTAL];
		for (int row = 0; row < VERTICAL; row++) {
			for (int col = 0; col < HORIZONTAL; col++) {
				setField(row, col, Disc.EMPTY);
			}
		}
	}

	// Queries

	/*
	 * @ ensures \result != this; ensures (\forall int i; 0 <= i & i < VERTICAL;
	 * \forall int j; 0 <= j & j < HORIZONTAL; \result.getField(i, j) ==
	 * this.getField(i, j));
	 */
	/**
	 * Creates a deep copy of this board.
	 */
	public Board deepCopy() {
		Board board = new Board();
		for (int row = 0; row < VERTICAL; row++) {
			for (int col = 0; col < HORIZONTAL; col++) {
				board.setField(row, col, getField(row, col));
			}
		}
		return board;
	}

	/*
	 * @ requires 0 <= col & col < VERTICAL;
	 */
	/**
	 * Calculates the lowest vertical empty row given the column if empty is
	 * true, or the highest full row if empty is false
	 * 
	 * @return the vertical index belonging to the field
	 */
	public int index(int col, boolean empty) {
		if (empty) {
			for (int row = VERTICAL - 1; row >= 0; row--) {
				if (getField(row, col) == Disc.EMPTY) {
					return row;
				}
			}
		} else {
			for (int row = 0; row < VERTICAL; row++) {
				if (getField(row, col) != Disc.EMPTY) {
					return row;
				}
			}
		}
		return -1;
	}

	/*
	 * @ ensures \result == (0 <= col && col < HORIZONTAL);
	 */
	/**
	 * Returns true if i is a valid column of the board
	 * 
	 * @return true if 0 <= i < HORIZONTAL
	 */
	/* @pure */
	public boolean isField(int col) {
		return 0 <= col && col < HORIZONTAL;
	}

	/*
	 * @ ensures \result == (0 <= row && row < VERTICAL && 0 <= col && col <
	 * HORIZONTAL);
	 */
	/**
	 * Returns true of the (row,col) pair refers to a valid field on the board.
	 * 
	 * @return true if 0 <= row < VERTICAL && 0 <= col < HORIZONTAL
	 */
	/* @pure */
	public boolean isField(int row, int col) {
		return 0 <= row && row < VERTICAL && 0 <= col && col < HORIZONTAL;
	}

	/*
	 * @ requires this.isField(row,col); ensures \result == Disc.EMPTY ||
	 * \result == Disc.YELLOW || \result == Disc.RED;
	 */
	/**
	 * Returns the content of the field referred to by the (row,col) pair.
	 * 
	 * @param row
	 *            the row of the field
	 * @param col
	 *            the column of the field
	 * @return the disc on the field
	 */
	public Disc getField(int row, int col) {
		if (isField(row, col)) {
			return fields[row][col];
		} else {
			return null;
		}
	}

	/*
	 * @ requires this.isField(row,col); ensures \result ==
	 * (this.getField(row,col) == Disc.EMPTY);
	 */
	/**
	 * Returns true if the field referred to by the (row,col) pair it empty.
	 * 
	 * @param row
	 *            the row of the field
	 * @param col
	 *            the column of the field
	 * @return true if the field is empty
	 */
	/* @pure */
	public boolean isEmptyField(int row, int col) {
		if (isField(row, col)) {
			return getField(row, col) == Disc.EMPTY;
		} else {
			return false;
		}
	}

	/*
	 * @ ensures \result == \forall int i; 0 <= i & i < VERTICAL; \forall int j;
	 * 0 <= j & j < HORIZONTAL; this.getField(i, j) != Disc.EMPTY);
	 */
	/**
	 * Tests if the whole board is full.
	 * 
	 * @return true if all fields are occupied
	 */
	/* @pure */
	public boolean isFull() {
		for (int row = 0; row < VERTICAL; row++) {
			for (int col = 0; col < HORIZONTAL; col++)
				if (getField(row, col) == Disc.EMPTY) {
					return false;
				}
		}
		return true;
	}

	/*
	 * @ ensures \result == this.isFull() || this.hasWinner();
	 */
	/**
	 * Returns true if the game is over. The game is over when there is a winner
	 * or the whole board is full.
	 * 
	 * @return true if the game is over
	 */
	/* @pure */
	public boolean gameOver() {
		return isFull() || hasWinner();
	}

	/**
	 * Checks whether there is a row with 4 or more discs d.
	 * 
	 * @param d
	 *            the disc of interest
	 * @return true if there is a row controlled by d
	 */
	public boolean hasRow(Disc d) {
		for (int row = 0; row < VERTICAL; row++) {
			int count = 0;
			for (int col = 0; HORIZONTAL + count - col >= ROW; col++) {
				if (getField(row, col) == d) {
					if (++count >= ROW) {
						return true;
					}
				} else {
					count = 0;
				}
			}
		}
		return false;
	}

	/**
	 * Checks whether there is a column with 4 or more discs d.
	 * 
	 * @param d
	 *            the disc of interest
	 * @return true if there is a column controlled by d
	 */
	public boolean hasColumn(Disc d) {
		for (int col = 0; col < HORIZONTAL; col++) {
			int count = 0;
			for (int row = 0; VERTICAL + count - row >= ROW; row++) {
				if (getField(row, col) == d) {
					if (++count >= ROW) {
						return true;
					}
				} else {
					count = 0;
				}
			}
		}
		return false;
	}

	/**
	 * Checks whether there is a diagonal with 4 or more discs d.
	 * 
	 * @param d
	 *            the disc of interest
	 * @return true if there is a diagonal controlled by d
	 */
	public boolean hasDiagonal(Disc d) {
		return hasUpperDiagonal(d) || hasLowerDiagonal(d);
	}

	public boolean hasUpperDiagonal(Disc d) {
		int r = VERTICAL - ROW;
		int c = 0;
		while (c < HORIZONTAL) {
			if (r > 0) {
				r--;
			} else {
				c++;
			}
			int count = 0;
			for (int row = r, col = c; VERTICAL + count - row >= ROW
					&& HORIZONTAL + count - col >= ROW; row++, col++) {
				if (getField(row, col) == d) {
					if (++count >= ROW) {
						return true;
					}
				} else {
					count = 0;
				}
			}
		}
		return false;
	}

	public boolean hasLowerDiagonal(Disc d) {
		int r = ROW - 1;
		int c = 0;
		while (c < HORIZONTAL) {
			if (r <= VERTICAL - 1) {
				r++;
			} else {
				c++;
			}
			int count = 0;
			for (int row = r, col = c; row + count + 1 >= ROW
					&& HORIZONTAL + count - col >= ROW; row--, col++) {
				if (getField(row, col) == d) {
					if (++count >= ROW) {
						return true;
					}
				} else {
					count = 0;
				}
			}
		}
		return false;
	}

	/*
	 * @ requires d == Disc.YELLOW | d == Disc.RED; ensures \result ==
	 * this.hasRow(d) || this.hasColumn(d) | this.hasDiagonal(d);
	 */
	/**
	 * Checks if the disc d has won. A disc wins if it controls at least one
	 * row, column or diagonal.
	 * 
	 * @param d
	 *            the disc of interest
	 * @return true if the disc has won
	 */
	/* @pure */
	public boolean isWinner(Disc d) {
		if (d == Disc.YELLOW || d == Disc.RED) {
			return hasRow(d) || hasColumn(d) || hasDiagonal(d);
		} else {
			return false;
		}
	}

	/*
	 * @ ensures \result == isWinner(Disc.YELLOW) | \result ==
	 * isWinner(Disc.RED);
	 */
	/**
	 * Returns true if the game has a winner. This is the case when one of the
	 * discs controls at least one row, column or diagonal.
	 * 
	 * @return true if the board has a winner.
	 */
	/* @pure */
	public boolean hasWinner() {
		return isWinner(Disc.YELLOW) || isWinner(Disc.RED);
	}

	/**
	 * Returns a String representation of this board. In addition to the current
	 * situation, the String also shows the numbering of the fields.
	 * 
	 * @return the game situation as String
	 */
	public String toString() {
		String output = "";
		for (Disc[] d : fields) {
			output += Arrays.toString(d) + "\n";
		}
		return output;
	}

	// -- Commands ---------------------------------------------------

	/*
	 * @ ensures (\forall int i; 0 <= i & i < VERTICAL * VERTICAL;
	 * this.getField(i) == Disc.EMPTY);
	 */
	/**
	 * Empties all fields of this board (i.e., let them refer to the value
	 * Disc.EMPTY).
	 */
	public void reset() {
		for (int row = 0; row < VERTICAL; row++) {
			for (int col = 0; col < HORIZONTAL; col++) {
				setField(row, col, Disc.EMPTY);
			}
		}
	}

	/*
	 * @ requires this.isField(col); ensures this.getField(i, j) == d;
	 */
	/**
	 * Sets the content of lowest empty field in the column to the disc d.
	 * 
	 * @param col
	 *            the field column
	 * @param d
	 *            the disc to be placed
	 */
	public void setField(int col, Disc d) {
		if (isField(col) && index(col, true) != -1) {
			fields[index(col, true)][col] = d;
		}
	}

	/*
	 * @ requires this.isField(row,col); ensures this.getField(row,col) == d;
	 */
	/**
	 * Sets the content of the field represented by the (row,col) pair to the
	 * disc <code>m</code>.
	 * 
	 * @param row
	 *            the field's row
	 * @param col
	 *            the field's column
	 * @param d
	 *            the disc to be placed
	 */
	public void setField(int row, int col, Disc d) {
		if (isField(row, col)) {
			fields[row][col] = d;
		}
	}

}
