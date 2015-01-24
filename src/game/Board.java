package game;

import java.util.Arrays;
import java.util.Observable;

/**
 * Board class for the Connect4 according to the protocol of the TI-2 group.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public class Board extends Observable {
	// Constants:
	/** the amount of discs needed next to eachother to win. */
	public static final int CONNECT = 4;

	// Instance variables:
	/** The amount of rows. */
	public int rows;

	/** The amount of columns. */
	public int columns;

	/**
	 * The rows by columns board of the connect4 game.
	 */
	private Disc[][] fields;

	/*@ private invariant fields.length == getRows() * getColumns();
		invariant (\forall int i; 0 <= i & i < getRows(); (\forall int j; 0 <= j & j < getColumns(); this.getField(i, j) == Disc.EMPTY || this.getField(i, j) == Disc.YELLOW || this.getField(i, j) == Disc.RED));
	*/

	// Constructors
	/**
	 * Creates an empty board with the default boardsize of 6 rows and 7
	 * columns.
	 */
	public Board() {
		this(6, 7);
	}

	/**
	 * Creates an empty board with the specified board size.
	 *
	 * @param rowsArg
	 *            the amount of rows of the specified board size
	 * @param columnsArg
	 *            the amount of rows of the specified board size
	 */
	//@ensures (\forall int i; 0 <= i & i < rows; (\forall int j; 0 <= j & j < columns; this.getField(i, j) == Disc.EMPTY));
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

	/**
	 * Returns the amount of rows this board has.
	 *
	 * @return the amount of rows
	 */
	/*@ pure */public int getRows() {
		return rows;
	}

	/**
	 * Returns the amount of columns this board has.
	 *
	 * @return the amount of columns
	 */
	/*@ pure */public int getColumns() {
		return columns;
	}

	// Queries:
	/**
	 * Creates a deep copy of this board.
	 *
	 * @return the board
	 */
	/*@ ensures \result != this;
		ensures (\forall int i; 0 <= i & i < rows; (\forall int j; 0 <= j & j < columns; \result.getField(i, j) == this.getField(i, j)));
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

	/**
	 * Calculates the lowest empty row given the column.
	 *
	 * @param col
	 *            the column
	 * @return the vertical index belonging to the row
	 */
	//@requires isField(col);
	/*@pure*/public int emptyRow(int col) {
		int emptyRow = -1;
		for (int row = rows - 1; row >= 0; row--) {
			if (getField(row, col) == Disc.EMPTY) {
				emptyRow = row;
				break;
			}
		}
		return emptyRow;
	}

	/**
	 * Calculates the highest full row given the column.
	 *
	 * @param col
	 *            the column
	 * @return the vertical index belonging to the row
	 */
	//@requires isField(col);
	/*@pure*/public int fullRow(int col) {
		int fullRow = -1;
		for (int row = 0; row < rows; row++) {
			if (getField(row, col) != Disc.EMPTY) {
				fullRow = row;
				break;
			}
		}
		return fullRow;
	}

	/**
	 * Returns true if col is a valid column of the board.
	 *
	 * @param col
	 *            the column
	 * @return true if the column exists
	 */
	//@ensures \result == (0 <= col && col < columns);
	/*@pure*/public boolean isField(int col) {
		return 0 <= col && col < columns;
	}

	/**
	 * Returns true of the (row,col) pair refers to a valid field on the board.
	 *
	 * @param row
	 *            the row
	 * @param col
	 *            the column
	 * @return true if both the row and the column exists
	 */
	//@ensures \result == (0 <= row && row < rows && 0 <= col && col < columns);
	/*@pure*/public boolean isField(int row, int col) {
		return 0 <= row && row < rows && 0 <= col && col < columns;
	}

	/**
	 * Returns the content of the field referred to by the (row,col) pair.
	 * 
	 * @param row
	 *            the row of the field
	 * @param col
	 *            the column of the field
	 * @return the disc of the field
	 */
	/*@ requires this.isField(row,col);
		ensures \result == Disc.EMPTY || \result == Disc.YELLOW || \result == Disc.RED;
	*/
	/*@pure*/public Disc getField(int row, int col) {
		return fields[row][col];
	}

	/**
	 * Returns true if there is an empty field in the column.
	 * 
	 * @param col
	 *            the column
	 * @return true if there is an empty field
	 */
	/*@ requires this.isField(col);
		ensures \result == (this.getField(emptyRow(col), col) == Disc.EMPTY);
	*/
	/*@pure*/public boolean isEmptyField(int col) {
		boolean hasEmpty = false;
		for (int row = 0; row < rows; row++) {
			if (isEmptyField(row, col)) {
				hasEmpty = true;
				break;
			}
		}
		return hasEmpty;
	}

	/**
	 * Returns true if the field referred to by the (row,col) pair is empty.
	 * 
	 * @param row
	 *            the row of the field
	 * @param col
	 *            the column of the field
	 * @return true if the field is empty
	 */
	/*@ requires this.isField(row,col);
		ensures \result == (this.getField(row,col) == Disc.EMPTY);
	*/
	/*@pure*/public boolean isEmptyField(int row, int col) {
		return getField(row, col) == Disc.EMPTY;
	}

	/**
	 * Tests if the whole board is full.
	 * 
	 * @return true if all fields are occupied
	 */
	//@ensures \result == (\forall int i; 0 <= i & i < rows; (\forall int j; 0 <= j & j < columns; this.getField(i, j) != Disc.EMPTY));
	/*@pure*/public boolean isFull() {
		boolean isFull = true;
		loop: for (int row = 0; row < rows; row++) {
			for (int col = 0; col < columns; col++) {
				if (getField(row, col) == Disc.EMPTY) {
					isFull = false;
					break loop;
				}
			}
		}
		return isFull;
	}

	/**
	 * Returns true if the game is over. The game is over when there is a winner
	 * or the whole board is full.
	 * 
	 * @return true if the game is over
	 */
	//@ensures \result == this.isFull() || this.hasWinner();
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
	//@ requires d == Disc.YELLOW | d == Disc.RED;
	/*@pure*/public boolean hasRow(Disc d) {
		boolean hasRow = false;
		loop: for (int row = 0; row < rows; row++) {
			int count = 0;
			for (int col = 0; columns + count - col >= CONNECT; col++) {
				if (getField(row, col) == d) {
					if (++count >= CONNECT) {
						hasRow = true;
						break loop;
					}
				} else {
					count = 0;
				}
			}
		}
		return hasRow;
	}

	/**
	 * Checks whether there is a column with 4 or more discs d.
	 * 
	 * @param d
	 *            the disc of interest
	 * @return true if there is a column controlled by d
	 */
	//@ requires d == Disc.YELLOW | d == Disc.RED;
	/*@pure*/public boolean hasColumn(Disc d) {
		boolean hasColumn = false;
		loop: for (int col = 0; col < columns; col++) {
			int count = 0;
			for (int row = 0; rows + count - row >= CONNECT; row++) {
				if (getField(row, col) == d) {
					if (++count >= CONNECT) {
						hasColumn = true;
						break loop;
					}
				} else {
					count = 0;
				}
			}
		}
		return hasColumn;
	}

	/**
	 * Checks whether there is an diagonal with 4 or more discs d.
	 * 
	 * @param d
	 *            the disc of interest
	 * @return true if there is a diagonal controlled by d
	 */
	//@ requires d == Disc.YELLOW | d == Disc.RED;
	/*@pure*/public boolean hasDiagonal(Disc d) {
		boolean hasDiagonal = false;
		int r = rows - CONNECT;
		int c = 0;
		loop: while (c < columns) {
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
							hasDiagonal = true;
							break loop;
						}
					} else {
						count1 = 0;
					}
				}
				if (diag2) {
					if (getField(rows - 1 - row, col) == d) {
						if (++count2 >= CONNECT) {
							hasDiagonal = true;
							break loop;
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
		return hasDiagonal;
	}

	/**
	 * Checks if the disc d has won. A disc wins if it controls at least one
	 * row, column or diagonal.
	 * 
	 * @param d
	 *            the disc of interest
	 * @return true if the disc has won
	 */
	/*@ requires d == Disc.YELLOW | d == Disc.RED;
		ensures \result == this.hasRow(d) | this.hasColumn(d) | this.hasDiagonal(d);
	*/
	/*@pure*/public boolean isWinner(Disc d) {
		return (d == Disc.YELLOW || d == Disc.RED)
				&& (hasRow(d) || hasColumn(d) || hasDiagonal(d));
	}

	/**
	 * Returns true if the game has a winner. This is the case when one of the
	 * discs controls at least one row, column or diagonal.
	 * 
	 * @return true if the board has a winner.
	 */
	//@ensures \result == isWinner(Disc.YELLOW) | \result == isWinner(Disc.RED);
	/*@pure*/public boolean hasWinner() {
		return isWinner(Disc.YELLOW) || isWinner(Disc.RED);
	}

	/**
	 * Returns a String representation of this board.
	 * 
	 * @return the game situation as String
	 */
	public String toString() {
		String output = "";
		for (Disc[] d : fields) {
			output += Arrays.toString(d) + "\n";
		}
		//TODO: Ondersteun custom board size hiermee.
		output += "[0  1  2  3  4  5  6]";
		return output;
	}

	/**
	 * Returns a String representation of this board following the protocol.
	 * 
	 * @return the game situation as String
	 */
	public String toProtocol() {
		String output = columns + " " + rows;
		// TODO: constantes?
		for (int row = rows - 1; row >= 0; row--) {
			for (int col = 0; col < columns; col++) {
				if (getField(row, col) == Disc.EMPTY) {
					output += " " + 0;
				} else if (getField(row, col) == Disc.YELLOW) {
					output += " " + 1;
				} else if (getField(row, col) == Disc.RED) {
					output += " " + 2;
				}
			}
		}
		return output;
	}

	/**
	 * Empties all fields of this board (i.e., let them refer to the value
	 * Disc.EMPTY).
	 */
	//@ensures (\forall int i; 0 <= i & i < rows; (\forall int j; 0 <= j & j < columns; this.getField(i, j) == Disc.EMPTY));
	public void reset() {
		for (int row = 0; row < rows; row++) {
			for (int col = 0; col < columns; col++) {
				setField(row, col, Disc.EMPTY);
			}
		}
	}

	/**
	 * Places disc d in the lowest empty row in the column col.
	 * 
	 * @param col
	 *            the field's column
	 * @param d
	 *            the disc to be placed
	 */
	/*@ requires d == Disc.YELLOW | d == Disc.RED;
		requires this.isField(col) & this.isEmptyField(col);
		ensures emptyRow(col) != -1 ? this.getField(emptyRow(col) - 1, col) == d : this.getField(rows - 1, col) == d;
	*/
	public void insertDisc(int col, Disc d) {
		int row = emptyRow(col);
		setField(row, col, d);
	}

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
	/*@ requires this.isField(row,col);
		ensures this.getField(row,col) == d;
	*/
	public void setField(int row, int col, Disc d) {
		fields[row][col] = d;
		super.setChanged();
		super.notifyObservers(new int[] { col, row });
	}

	/**
	 * Compares 2 boards, and returns true if they're the same.
	 * 
	 * @param compareTo
	 *            The board this is compared to.
	 * @return true if this and compareTo are equal.
	 */
	public boolean equals(Board compareTo) {
		boolean equals = true;
		int columns = this.getColumns();
		int rows = this.getRows();
		if (columns == compareTo.getColumns() && rows == compareTo.getRows()) {
			for (int col = 0; col < columns; col++) {
				for (int row = 0; row < rows; row++) {
					if (this.getField(row, col) != compareTo.getField(row, col)) {
						equals = false;
					}
				}
			}
		} else {
			equals = false;
		}
		return equals;
	}
}
