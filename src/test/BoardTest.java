package test;

import static org.junit.Assert.assertEquals;
import game.Board;
import game.Disc;

import org.junit.Before;
import org.junit.Test;

/**
 * Test program for Board.java. <br>
 * <br>
 * WARNING: THIS TEST CANNOT BE RELIABLY USED FOR BOARDS WITH OTHER SIZES THAN
 * THE DEFAULT 7 COLUMNS BY 6 ROWS <br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public class BoardTest {
	/**
	 * Test variable for a Board object.
	 */
	private Board b;

	/**
	 * This method creates a new Board before each test.
	 * 
	 * @throws Exception
	 *             Any general exception.
	 */
	@Before
	public void setUp() throws Exception {
		b = new Board();
	}

	/**
	 * Tests if a new Board is actually empty, by calling b.getField(row, col)
	 * for every valid field in the Board, and checking if that returns
	 * Disc.EMPTY.
	 */
	@Test
	public void testEmptyBoard() {
		for (int row = 0; row < b.getRows(); row++) {
			for (int col = 0; col < b.getColumns(); col++) {
				assertEquals("b.getField(" + row + "," + col + ")",
						b.getField(row, col), Disc.EMPTY);
			}
		}
	}

	/**
	 * Tests the method deepCopy(). It inserts some Discs in the original Board,
	 * then creates a copy of it (using b.deepCopy()). After that it makes sure
	 * that every Disc is the same in both Boards.
	 */
	@Test
	public void testDeepCopy() {
		b.insertDisc(1, Disc.YELLOW);
		b.insertDisc(3, Disc.RED);
		Board copy = b.deepCopy();
		for (int row = 0; row < b.getRows(); row++) {
			for (int col = 0; col < b.getColumns(); col++) {
				assertEquals(
						"For all fields: b.getField(row, col) == copy.getField(row, col)",
						b.getField(row, col), copy.getField(row, col));
			}
		}
	}

	/**
	 * Tests the method emptyRow(col). First it assures that emptyRow returns 5
	 * for all columns on an empty Board, since 5 is the lowest row on the
	 * Board. It then inserts a Disc into column 2, and assures that for all
	 * columns, except for 2, the emptyRow still returns 5. For column 2, this
	 * should now return 4 instead. After this, some more Discs are inserted,
	 * and a similar test is executed. The final test tests whether emptyRow
	 * returns -1 when the specified column is full, as it's supposed to do.
	 */
	@Test
	public void testEmptyRow() {
		for (int col = 0; col < b.getColumns(); col++) {
			assertEquals("For all empty columns: b.emptyRow(col) == 5", 5,
					b.emptyRow(col));
		}
		b.insertDisc(2, Disc.YELLOW);
		for (int col = 0; col < b.getColumns(); col++) {
			if (col != 2) {
				assertEquals("For all empty columns: b.emptyRow(col) == 5", 5,
						b.emptyRow(col));
			} else {
				assertEquals("For col = 2: b.emptyRow(col) == 4 now", 4,
						b.emptyRow(col));
			}
		}
		b.insertDisc(2, Disc.RED);
		b.insertDisc(2, Disc.YELLOW);
		b.insertDisc(5, Disc.RED);
		b.insertDisc(1, Disc.RED);
		b.insertDisc(1, Disc.YELLOW);
		b.insertDisc(1, Disc.RED);
		b.insertDisc(1, Disc.YELLOW);
		b.insertDisc(1, Disc.YELLOW);
		for (int col = 0; col < b.getColumns(); col++) {
			if (col != 2 && col != 5 && col != 1) {
				assertEquals("For all empty columns: b.emptyRow(col) == 5", 5,
						b.emptyRow(col));
			} else if (col == 2) {
				assertEquals("For col = 2: b.emptyRow(col) == 2 now", 2,
						b.emptyRow(col));
			} else if (col == 5) {
				assertEquals("For col = 5: b.emptyRow(col) == 4 now", 4,
						b.emptyRow(col));
			} else if (col == 1) {
				assertEquals("For col = 1: b.emptyRow(col) == 0 now", 0,
						b.emptyRow(col));
			}
		}
		b.reset();
		for (int row = 0; row < b.getRows(); row++) {
			b.insertDisc(0, Disc.RED);
		}
		assertEquals("b.emptyRow(0)", -1, b.emptyRow(0));
	}

	/**
	 * Tests the method fullRow(col). First, it assures that the method returns
	 * -1 for every column on an empty Board, since there's no Discs in any
	 * column. After that, some Discs are inserted, and it's assured that for
	 * the columns those were inserted into, b.fullRow(col) returns the values
	 * it's supposed to.
	 */
	@Test
	public void testFullRow() {
		for (int col = 0; col < b.getColumns(); col++) {
			assertEquals("b.fullRow(col) should be -1 when there are no discs",
					-1, b.fullRow(col));
		}
		b.insertDisc(2, Disc.RED);
		b.insertDisc(2, Disc.YELLOW);
		b.insertDisc(5, Disc.RED);
		b.insertDisc(1, Disc.RED);
		b.insertDisc(1, Disc.YELLOW);
		b.insertDisc(1, Disc.RED);
		b.insertDisc(1, Disc.YELLOW);
		b.insertDisc(1, Disc.YELLOW);
		assertEquals("b.fullRow(1) == 1", 1, b.fullRow(1));
		assertEquals("b.fullRow(2) == 4", 4, b.fullRow(2));
		assertEquals("b.fullRow(5) == 5", 5, b.fullRow(5));
	}

	/**
	 * Firstly tests the method isField(col). First, it tests for every valid
	 * column, that it's a valid column. Afterwards, it tests the same for some
	 * invalid columns.
	 * 
	 * Secondly tests the method isField(row, col). First, it tests for every
	 * valid column and row, that they're valid. Afterwards, it tests the same
	 * for some invalid ones.
	 */
	@Test
	public void testIsField() {
		// Calling isField(col) with a valid index
		for (int col = 0; col < b.getColumns(); col++) {
			assertEquals("b.isField(col)", true, b.isField(col));
		}
		// Calling isField(col) with an invalid index

		for (int col = b.getColumns(); col < b.getColumns() * 2; col++) {
			assertEquals("For these invalid fields: b.isField(col) == false",
					false, b.isField(col));
		}

		// Calling isField(row, col) with a valid index
		for (int row = 0; row < b.getRows(); row++) {
			for (int col = 0; col < b.getColumns(); col++) {
				assertEquals(
						"For all valid fields: b.isField(row, col) == true",
						true, b.isField(row, col));
			}
		}
		// Calling isField(row, col) with some invalid indexes
		for (int row = b.getRows(); row < b.getRows() * 2; row++) {
			for (int col = b.getColumns(); col < b.getColumns() * 2; col++) {
				assertEquals(
						"For these invalid fields: b.isField(row, col) == false",
						false, b.isField(row, col));
			}
		}
	}

	/**
	 * Tests the method getField(row, col). First, it assures that on an empty
	 * Board, b.getField(row, col) returns Disc.EMPTY for every row and column.
	 * After that, the Board is filled with some Discs. Then, it's tested that
	 * b.getField(row, col) returns the Discs it's intended to return.
	 */
	@Test
	public void testGetField() {
		// Calls all fields, and checks if they're Disc.EMPTY
		for (int row = 0; row < b.getRows(); row++) {
			for (int col = 0; col < b.getColumns(); col++) {
				assertEquals(
						"For all fields on an empty board: b.getField(row, col) == Disc.EMPTY",
						Disc.EMPTY, b.getField(row, col));
			}
		}
		// Fills the board with some Discs
		b.insertDisc(2, Disc.RED);
		b.insertDisc(2, Disc.YELLOW);
		b.insertDisc(5, Disc.RED);
		b.insertDisc(1, Disc.RED);
		b.insertDisc(1, Disc.YELLOW);
		b.insertDisc(1, Disc.RED);
		b.insertDisc(1, Disc.YELLOW);
		b.insertDisc(1, Disc.YELLOW);
		// Tests if the getField returns the proper Discs
		assertEquals("In (4,2) there's now a YELLOW Disc", Disc.YELLOW,
				b.getField(4, 2));
		assertEquals("In (5,2) there's now a RED Disc", Disc.RED,
				b.getField(5, 2));
		assertEquals("In (5,5) there's now a RED Disc", Disc.RED,
				b.getField(5, 5));
		assertEquals("In (1,1) there's now a YELLOW Disc", Disc.YELLOW,
				b.getField(1, 1));
		assertEquals("In (2,1) there's now a YELLOW Disc", Disc.YELLOW,
				b.getField(2, 1));
		assertEquals("In (3,1) there's now a RED Disc", Disc.RED,
				b.getField(3, 1));
		assertEquals("In (4,1) there's now a YELLOW Disc", Disc.YELLOW,
				b.getField(4, 1));
		assertEquals("In (5,1) there's now a RED Disc", Disc.RED,
				b.getField(5, 1));
	}

	/**
	 * Firstly, it tests the method isEmptyField(col). It tests that for every
	 * column on an empty Board there's at least 1 empty field in each of those
	 * columns. Then, a column is filled, and after each Disc, it's checked
	 * whether the column still has empty fields. Once the column is full, it
	 * should no longer have empty fields.
	 * 
	 * Secondly, it tests the method isEmptyField(row, col). First, it assures
	 * that every field on an empty Board is empty. After that it inserts some
	 * Discs, and assures that the fields those Discs got inserted into are no
	 * longer empty.
	 */
	@Test
	public void testIsEmptyField() {
		for (int col = 0; col < b.getColumns(); col++) {
			assertEquals(true, b.isEmptyField(col));
		}
		for (int row = 0; row < b.getRows(); row++) {
			assertEquals(true, b.isEmptyField(0));
			b.insertDisc(0, Disc.RED);
		}
		assertEquals(false, b.isEmptyField(0));
		// From here on testing isEmptyField(row, col)
		b.reset();
		for (int row = 0; row < b.getRows(); row++) {
			for (int col = 0; col < b.getColumns(); col++) {
				assertEquals(true, b.isEmptyField(row, col));
			}
		}
		// Inserts some discs
		b.insertDisc(2, Disc.RED);
		b.insertDisc(2, Disc.YELLOW);
		b.insertDisc(5, Disc.RED);
		b.insertDisc(1, Disc.RED);
		b.insertDisc(1, Disc.YELLOW);
		b.insertDisc(1, Disc.RED);
		b.insertDisc(1, Disc.YELLOW);
		b.insertDisc(1, Disc.YELLOW);
		assertEquals("(4,2) is no longer an empty field.", false,
				b.isEmptyField(4, 2));
		assertEquals("(5,2) is no longer an empty field.", false,
				b.isEmptyField(5, 2));
		assertEquals("(5,5) is no longer an empty field.", false,
				b.isEmptyField(5, 5));
		assertEquals("(1,1) is no longer an empty field.", false,
				b.isEmptyField(1, 1));
		assertEquals("(2,1) is no longer an empty field.", false,
				b.isEmptyField(2, 1));
		assertEquals("(3,1) is no longer an empty field.", false,
				b.isEmptyField(3, 1));
		assertEquals("(4,1) is no longer an empty field.", false,
				b.isEmptyField(4, 1));
		assertEquals("(5,1) is no longer an empty field.", false,
				b.isEmptyField(5, 1));
	}

	/**
	 * Tests the method isFull(). It puts a random Disc on every position of the
	 * Board. After each placement, a check is made to see that the Board is not
	 * full yet. After every Disc has been placed, the Board should be full.
	 */

	@Test
	public void testIsFull() {
		for (int row = 0; row < b.getRows(); row++) {
			for (int col = 0; col < b.getColumns(); col++) {
				if (Math.random() > 0.5) {
					b.setField(row, col, Disc.RED);
				} else {
					b.setField(row, col, Disc.YELLOW);
				}
				if (!(row == b.getRows() - 1 && col == b.getColumns() - 1)) {
					assertEquals("For a non-full board: b.isFull() == false",
							false, b.isFull());
				} else {
					assertEquals("For a full board: b.isFull() == true", true,
							b.isFull());
				}
			}
		}
	}

	/**
	 * Tests the method gameOver(). It wasn't necessary to implement a test for
	 * this method, since it only returns whether the Board isFull() or
	 * hasWinner(). These methods have been tested already.
	 */
	@Test
	public void testIsGameOver() {
	}

	/**
	 * Tests the method hasRow(Disc). It basically creates every possible
	 * situation, in which there's a row on the Board. At every boardrow, there
	 * are 4 potential rows, namely on the positions 0-3, 1-4, 2-5 and 3-6. To
	 * make every possible combination, the algorithm works as follows: Reset
	 * the Board before every test, then for every single boardrow, put 4 discs
	 * in that boardrow, such that there's 4 Discs connected. Then, check
	 * whether b.hasRow(Disc) is true for the Disc you inserted, and make sure
	 * (because why not) that for the Disc you didn't insert,
	 * b.hasRow(otherDisc) is false. After this, the same test is done, but with
	 * 3 Discs connected at a time. None of these should make b.hasRow(Disc) or
	 * b.hasRow(otherDisc) return true. After this, a pre-defined realistic
	 * situation is created, in which there's no 4 connected Discs for either of
	 * the players in a row, and it's made sure, that b.hasRow(Disc) and
	 * b.hasRow(otherDisc) are false.
	 */
	@Test
	public void testHasRow() {
		for (int row = 0; row < b.getRows(); row++) {
			for (int col = 0; col <= 3; col++) {
				b.reset();
				for (int i = col; i <= (col + 3); i++) {
					b.setField(row, i, Disc.RED);
				}
				// Red should now have a row, although yellow obviously
				// shouldn't.
				assertEquals("b.hasRow(Disc.RED) == true", true,
						b.hasRow(Disc.RED));
				assertEquals("b.hasRow(Disc.YELLOW) == false", false,
						b.hasRow(Disc.YELLOW));
			}
		}
		// Now tests with rows of 3.
		for (int row = 0; row < b.getRows(); row++) {
			for (int col = 0; col <= 3; col++) {
				b.reset();
				// Fill the boardrow with a row of 3 discs
				for (int i = col; i <= (col + 2); i++) {
					b.setField(row, i, Disc.RED);
				}
				assertEquals("b.hasRow(Disc.RED) == false", false,
						b.hasRow(Disc.RED));
				assertEquals("b.hasRow(Disc.YELLOW) == false", false,
						b.hasRow(Disc.YELLOW));

			}
			// Fills a clean board with some Discs which don't give a situation
			// where there's a row.
			b.reset();
			b.insertDisc(2, Disc.RED);
			b.insertDisc(2, Disc.YELLOW);
			b.insertDisc(5, Disc.RED);
			b.insertDisc(1, Disc.RED);
			b.insertDisc(1, Disc.YELLOW);
			b.insertDisc(1, Disc.RED);
			assertEquals("b.hasRow(Disc.RED) == false", false,
					b.hasRow(Disc.RED));
			assertEquals("b.hasRow(Disc.YELLOW) == false", false,
					b.hasRow(Disc.YELLOW));
		}
	}

	/**
	 * Tests the method hasColumn(Disc). It basically creates every possible
	 * situation, in which there's a column on the Board. At every boardcolumn,
	 * there are 3 potential columns, namely on the positions 0-3, 1-4 and 2-5.
	 * To make every possible combination, the algorithm works as follows: Reset
	 * the Board before every test, then for every single boardcolumn, put 4
	 * discs in that boardcolumn, such that there's 4 Discs connected. Then,
	 * check whether b.hasColumn(Disc) is true for the Disc you inserted, and
	 * make sure (because why not) that for the Disc you didn't insert,
	 * b.hasColumn(otherDisc) is false. After this, the same test is done, but
	 * with 3 Discs connected at a time. None of these should make
	 * b.hasColumn(Disc) or b.hasColumn(otherDisc) return true. After this, a
	 * pre-defined realistic situation is created, in which there's no 4
	 * connected Discs for either of the players in a column, and it's made
	 * sure, that b.hasColumn(Disc) and b.hasColumn(otherDisc) are false.
	 */
	@Test
	public void testHasColumn() {
		for (int col = 0; col < b.getColumns(); col++) {
			for (int row = 0; row <= 2; row++) {
				b.reset();
				for (int i = row; i <= (row + 3); i++) {
					b.setField(i, col, Disc.RED);
				}
				// Red should now have a row, although yellow obviously
				// shouldn't.
				assertEquals("b.hasColumn(Disc.RED) == true", true,
						b.hasColumn(Disc.RED));
				assertEquals("b.hasColumn(Disc.YELLOW) == false", false,
						b.hasColumn(Disc.YELLOW));
			}
		}
		// Now tests with columns of 3.
		for (int col = 0; col < b.getColumns(); col++) {
			for (int row = 0; row <= 2; row++) {
				b.reset();
				// Fill the boardcolumn with a row of 3 discs
				for (int i = row; i <= (row + 2); i++) {
					b.setField(i, col, Disc.RED);
				}
				assertEquals("b.hasColumn(Disc.RED) == false", false,
						b.hasColumn(Disc.RED));
				assertEquals("b.hasColumn(Disc.YELLOW) == false", false,
						b.hasColumn(Disc.YELLOW));
			}
		}
		// Fills a clean board with some Discs which don't give a situation
		// where there's a column.
		b.reset();
		b.insertDisc(2, Disc.RED);
		b.insertDisc(2, Disc.YELLOW);
		b.insertDisc(5, Disc.RED);
		b.insertDisc(1, Disc.RED);
		b.insertDisc(1, Disc.YELLOW);
		b.insertDisc(1, Disc.RED);
		assertEquals("b.hasColumn(Disc.RED) == false", false,
				b.hasColumn(Disc.RED));
		assertEquals("b.hasColumn(Disc.YELLOW) == false", false,
				b.hasColumn(Disc.YELLOW));
	}

	/**
	 * Tests the method hasDiagonal(). It basically creates every possible
	 * situation, in which there's a diagonal on the Board . The way it does the
	 * test, is as follows: it inserts 4 Disc s into the Board, which make the
	 * Board have a diagonal. After each Disc is inserted, a check is made, to
	 * see whether the Board has a diagonal. After each of the first three
	 * Discs, the Board should not have a diagonal, but after the fourth Disc,
	 * the Board should have one. Since there were only 24 options, each option
	 * was coded manually. This was humanly faster, than writing an algorithm
	 * for it. All possible diagonals can be found in the Excel-speadsheet
	 * located in /doc/PossibleDiagonals.xlsx. The numbers of the options in the
	 * code represent the numbers of options in the spreadsheet.
	 */
	@Test
	public void testHasDiagonal() {
		// Option 1
		b.setField(3, 0, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(2, 1, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(1, 2, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(0, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 2
		b.setField(4, 0, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(3, 1, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(2, 2, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(1, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 3
		b.setField(3, 1, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(2, 2, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(1, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(0, 4, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 4
		b.setField(5, 0, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(4, 1, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(3, 2, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(2, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 5
		b.setField(4, 1, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(3, 2, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(2, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(1, 4, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 6
		b.setField(3, 2, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(2, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(1, 4, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(0, 5, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 7
		b.setField(5, 1, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(4, 2, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(3, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(2, 4, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 8
		b.setField(4, 2, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(3, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(2, 4, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(1, 5, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 9
		b.setField(3, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(2, 4, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(1, 5, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(0, 6, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 10
		b.setField(5, 2, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(4, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(3, 4, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(2, 5, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 11
		b.setField(4, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(3, 4, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(2, 5, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(1, 6, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 12
		b.setField(5, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(4, 4, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(3, 5, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(2, 6, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// From now on testing the verticals the other way around.
		// Option 13
		b.setField(2, 0, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(3, 1, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(4, 2, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(5, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 14
		b.setField(1, 0, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(2, 1, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(3, 2, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(4, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 15
		b.setField(2, 1, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(3, 2, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(4, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(5, 4, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 16
		b.setField(0, 0, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(1, 1, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(2, 2, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(3, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 17
		b.setField(1, 1, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(2, 2, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(3, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(4, 4, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 18
		b.setField(2, 2, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(3, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(4, 4, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(5, 5, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 19
		b.setField(0, 1, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(1, 2, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(2, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(3, 4, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 20
		b.setField(1, 2, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(2, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(3, 4, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(4, 5, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 21
		b.setField(2, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(3, 4, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(4, 5, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(5, 6, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 22
		b.setField(0, 2, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(1, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(2, 4, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(3, 5, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 23
		b.setField(1, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(2, 4, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(3, 5, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(4, 6, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
		// Option 24
		b.setField(0, 3, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(1, 4, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(2, 5, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==false", false,
				b.hasDiagonal(Disc.RED));
		b.setField(3, 6, Disc.RED);
		assertEquals("b.hasDiagonal(Disc.RED)==true", true,
				b.hasDiagonal(Disc.RED));
		b.reset();
	}

	/**
	 * Tests the method isWinner(Disc). It wasn't necessary to implement a test
	 * for this method, since it only returns whether the Board hasRow(d) or
	 * hasColumn(d) or hasDiagonal(d). These methods have been tested already.
	 */
	@Test
	public void testIsWinner() {
	}

	/**
	 * Tests the method hasWinner(Disc). It wasn't necessary to implement a test
	 * for this method, since it only returns whether isWinner(Disc.YELLOW) or
	 * isWinner(Disc.RED). This method has been tested already.
	 */
	@Test
	public void testHasWinner() {
	}

	/**
	 * Tests the method hasWinner(Disc). It wasn't necessary to implement a test
	 * for this method, since it's implicitly tested.
	 */
	@Test
	public void testToString() {
	}

	/**
	 * Tests the method reset(). It basically fills the board with random Discs,
	 * it calls the method b.reset() and it tests if all the fields on the board
	 * are Disc.EMPTY afterwards.
	 */
	@Test
	public void testReset() {
		// Fills the board with Discs
		for (int row = 0; row < b.getRows(); row++) {
			for (int col = 0; col < b.getColumns(); col++) {
				if (Math.random() > 0.5) {
					b.setField(row, col, Disc.RED);
				} else {
					b.setField(row, col, Disc.YELLOW);
				}
			}
		}
		// Resets the board
		b.reset();
		// Tests if all fields are empty now.
		for (int row = 0; row < b.getRows(); row++) {
			for (int col = 0; col < b.getColumns(); col++) {
				assertEquals("All discs on the board are Disc.EMPTY now.",
						Disc.EMPTY, b.getField(row, col));
			}
		}
	}

	/**
	 * Tests the method insertDisc(col). It fills a column with a couple of
	 * Discs, and then makes sure that the inserted Discs are now in the places
	 * they should be.
	 */
	@Test
	public void testInsertDisc() {
		for (int row = 5; row >= 0; row--) {
			b.insertDisc(0, Disc.RED);
			assertEquals("b.getField(row, 0) == Disc.RED", Disc.RED,
					b.getField(row, 0));
		}
	}

	/**
	 * Tests the method setField(Disc). It basically places some Discs on the
	 * Board, and then checks whether the field it just placed it on has the
	 * proper Disc in it.
	 */
	@Test
	public void testSetField() {
		for (int row = 0; row < b.getRows(); row++) {
			for (int col = 0; col < b.getColumns(); col++) {
				b.setField(row, col, Disc.RED);
				assertEquals("b.getField(row, col) == Disc.RED", Disc.RED,
						b.getField(row, col));
			}
		}
	}
}