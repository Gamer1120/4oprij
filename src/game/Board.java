package game;

import java.util.Arrays;

/**
 * Board for the connect4 game.
 * 
 * @author Sven Konings en Michael Koopman
 * @version $Revision: 1.0 $
 */
public class Board {
	//TODO: support meerdere grotes
	// Constants:
	public static final int CONNECT = 4;

	// Instance variables:
	public int rows;
	public int columns;
	/*@
		private invariant fields.length == rows * columns;
		invariant (\forall int i; 0 <= i & i < rows; (\forall int j; 0 <= j & j < columns; this.getField(i, j) == Disc.EMPTY || this.getField(i, j) == Disc.YELLOW || this.getField(i, j) == Disc.RED));
	 */
	/**
	 * The rows by columns board of the connect4 game.
	 */
	private Disc[][] fields;

	// Constructors
	/*@ensures (\forall int i; 0 <= i & i < rows; (\forall int j; 0 <= j & j < columns; this.getField(i, j) == Disc.EMPTY));*/
	/**
	 * Creates an empty board.
	 */
	public Board() {
		this(6, 7);
	}

	/*@ensures (\forall int i; 0 <= i & i < rows; (\forall int j; 0 <= j & j < columns; this.getField(i, j) == Disc.EMPTY));*/
	/**
	 * Creates an empty board.
	 */
	public Board(int rowsArg, int columnsArg) {
		this.rows = rowsArg;
		this.columns = columnsArg;
		fields = new Disc[rows][columns];
		for (int row = 0; row < rows; row++) {
			for (int col = 0; col < columns; col++) {
				setField(row, col, Disc.EMPTY);
			}
		}
	}

	//TODO: javadoc en jml
	/*@ pure */public int getRows() {
		return rows;
	}

	//TODO: javadoc en jml
	/*@ pure */public int getColumns() {
		return columns;
	}

	// Queries:
	/*@
		ensures \result != this;
		ensures (\forall int i; 0 <= i & i < rows; (\forall int j; 0 <= j & j < columns; \result.getField(i, j) == this.getField(i, j)));
	 */
	/**
	 * Creates a deep copy of this board.
	 */
	public Board deepCopy() {
		Board board = new Board(rows, columns);
		for (int row = 0; row < rows; row++) {
			for (int col = 0; col < columns; col++) {
				board.setField(row, col, getField(row, col));
			}
		}
		return board;
	}

	/*@requires 0 <= col & col < rows;*/
	/**
	 * Calculates the lowest empty row given the column
	 * 
	 * @return the vertical index belonging to the row
	 */
	/*@pure*/public int emptyRow(int col) {
		for (int row = rows - 1; row >= 0; row--) {
			if (getField(row, col) == Disc.EMPTY) {
				return row;
			}
		}
		return -1;
	}

	/*@requires 0 <= col & col < rows;*/
	/**
	 * Calculates the highest full row given the column
	 * 
	 * @return the vertical index belonging to the row
	 */
	/*@pure*/public int fullRow(int col) {
		for (int row = 0; row < rows; row++) {
			if (getField(row, col) != Disc.EMPTY) {
				return row;
			}
		}
		return -1;
	}

	// TODO: Discuss whether or not to rename this to isColumn.
	/*@ensures \result == (0 <= col && col < columns);*/
	/**
	 * Returns true if col is a valid column of the board
	 * 
	 * @return true if 0 <= col < columns
	 */
	/*@pure*/public boolean isField(int col) {
		return 0 <= col && col < columns;
	}

	/*@ensures \result == (0 <= row && row < rows && 0 <= col && col < columns);*/
	/**
	 * Returns true of the (row,col) pair refers to a valid field on the board.
	 * 
	 * @return true if 0 <= row < rows && 0 <= col < columns
	 */
	/*@pure*/public boolean isField(int row, int col) {
		return 0 <= row && row < rows && 0 <= col && col < columns;
	}

	/*@
		requires this.isField(row,col);
		ensures \result == Disc.EMPTY || \result == Disc.YELLOW || \result == Disc.RED;
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
	/*@pure*/public Disc getField(int row, int col) {
		return fields[row][col];
	}

	//TODO: Discuss whether to rename this method to hasEmptyField(col).
	/*@
	requires this.isField(row,col);
	ensures \result == (this.getField(row,col) == Disc.EMPTY);
	*/
	/**
	 * Returns true if there is an empty field in the row.
	 * 
	 * @param col
	 *            the column of the field
	 * @return true if the field is empty
	 */
	/*@pure*/public boolean isEmptyField(int col) {
		for (int row = 0; row < rows; row++) {
			if (getField(row, col) == Disc.EMPTY) {
				return true;
			}
		}
		return false;
	}

	/*@
		requires this.isField(row,col);
		ensures \result == (this.getField(row,col) == Disc.EMPTY);
	 */
	/**
	 * Returns true if the field referred to by the (row,col) pair is empty.
	 * 
	 * @param row
	 *            the row of the field
	 * @param col
	 *            the column of the field
	 * @return true if the field is empty
	 */
	/*@pure*/public boolean isEmptyField(int row, int col) {
		return isField(row, col) && getField(row, col) == Disc.EMPTY;
	}

	/*@ensures \result == (\forall int i; 0 <= i & i < rows; (\forall int j; 0 <= j & j < columns; this.getField(i, j) != Disc.EMPTY));*/
	/**
	 * Tests if the whole board is full.
	 * 
	 * @return true if all fields are occupied
	 */
	/*@pure*/public boolean isFull() {
		for (int row = 0; row < rows; row++) {
			for (int col = 0; col < columns; col++) {
				if (getField(row, col) == Disc.EMPTY) {
					return false;
				}
			}
		}
		return true;
	}

	/*@ensures \result == this.isFull() || this.hasWinner();*/
	/**
	 * Returns true if the game is over. The game is over when there is a winner
	 * or the whole board is full.
	 * 
	 * @return true if the game is over
	 */
	/*@pure*/public boolean gameOver() {
		return isFull() || hasWinner();
	}

	/**
	 * Checks whether there is a row with 4 or more discs d.
	 * 
	 * @param d
	 *            the disc of interest
	 * @return true if there is a row controlled by d
	 */
	/*@pure*/public boolean hasRow(Disc d) {
		for (int row = 0; row < rows; row++) {
			int count = 0;
			for (int col = 0; columns + count - col >= CONNECT; col++) {
				if (getField(row, col) == d) {
					if (++count >= CONNECT) {
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
	/*@pure*/public boolean hasColumn(Disc d) {
		for (int col = 0; col < columns; col++) {
			int count = 0;
			for (int row = 0; rows + count - row >= CONNECT; row++) {
				if (getField(row, col) == d) {
					if (++count >= CONNECT) {
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
	 * Checks whether there is an diagonal with 4 or more discs d.
	 * 
	 * @param d
	 *            the disc of interest
	 * @return true if there is a diagonal controlled by d
	 */
	/*@pure*/public boolean hasDiagonal(Disc d) {
		int r = rows - CONNECT;
		int c = 0;
		while (c < columns) {
			int row = r;
			int col = c;
			int count1 = 0;
			int count2 = 0;
			boolean diag1 = (rows + count1 - row >= CONNECT)
					&& (columns + count1 - col >= CONNECT);
			boolean diag2 = (rows + count2 - row >= CONNECT)
					&& (columns + count2 - col >= CONNECT);
			while (diag1 || diag2) {
				if (diag1) {
					if (getField(row, col) == d) {
						if (++count1 >= CONNECT) {
							return true;
						}
					} else {
						count1 = 0;
					}
				}
				if (diag2) {
					if (getField(rows - 1 - row, col) == d) {
						if (++count2 >= CONNECT) {
							return true;
						}
					} else {
						count2 = 0;
					}
				}
				row++;
				col++;
				diag1 = (rows + count1 - row >= CONNECT)
						&& (columns + count1 - col >= CONNECT);
				diag2 = (rows + count2 - row >= CONNECT)
						&& (columns + count2 - col >= CONNECT);
			}
			if (r > 0) {
				r--;
			} else {
				c++;
			}
		}
		return false;
	}

	/*@
		requires d == Disc.YELLOW | d == Disc.RED;
		ensures \result == this.hasRow(d) || this.hasColumn(d) | this.hasDiagonal(d);
	 */
	/**
	 * Checks if the disc d has won. A disc wins if it controls at least one
	 * row, column or diagonal.
	 * 
	 * @param d
	 *            the disc of interest
	 * @return true if the disc has won
	 */
	/*@pure*/public boolean isWinner(Disc d) {
		return (d == Disc.YELLOW || d == Disc.RED)
				&& (hasRow(d) || hasColumn(d) || hasDiagonal(d));
	}

	/*@ensures \result == isWinner(Disc.YELLOW) | \result == isWinner(Disc.RED);*/
	/**
	 * Returns true if the game has a winner. This is the case when one of the
	 * discs controls at least one row, column or diagonal.
	 * 
	 * @return true if the board has a winner.
	 */
	/*@pure*/public boolean hasWinner() {
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

	/*@ensures (\forall int i; 0 <= i & i < rows; (\forall int j; 0 <= j & j < columns; this.getField(i, j) == Disc.EMPTY));*/
	/**
	 * Empties all fields of this board (i.e., let them refer to the value
	 * Disc.EMPTY).
	 */
	public void reset() {
		for (int row = 0; row < rows; row++) {
			for (int col = 0; col < columns; col++) {
				setField(row, col, Disc.EMPTY);
			}
		}
	}

	/*@
		requires this.isField(col) & this.isEmptyField(col);
		ensures (\forall int i; 0 <= i & i < rows; (\forall int j; 0 <= j & j < columns; this.getField(i, j) == d));
	 */
	/**
	 * Places disc d in the lowest empty row in the column col.
	 * 
	 * @param col
	 *            the field column
	 * @param d
	 *            the disc to be placed
	 */
	public void insertDisc(int col, Disc d) {
		fields[emptyRow(col)][col] = d;
	}

	/*@
		requires this.isField(row,col);
		ensures this.getField(row,col) == d;
	 */
	/**
	 * Sets the content of the field represented by the (row,col) pair to the
	 * disc m.
	 * 
	 * @param row
	 *            the field's row
	 * @param col
	 *            the field's column
	 * @param d
	 *            the disc to be placed
	 */
	public void setField(int row, int col, Disc d) {
		fields[row][col] = d;
	}

}
