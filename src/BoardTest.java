import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

public class BoardTest {
	private Board b;

	@Before
	public void setUp() throws Exception {
		b = new Board();
	}

	@Test
	public void testEmptyBoard() {
		for (int row = 0; row < Board.VERTICAL; row++) {
			for (int col = 0; col < Board.HORIZONTAL; col++) {
				assertEquals("b.getField(" + row + "," + col + ")",
						b.getField(row, col), Disc.EMPTY);
			}
		}
	}

	@Test
	public void testDeepCopy() {
		b.insertDisc(1, Disc.YELLOW);
		b.insertDisc(3, Disc.RED);
		Board copy = b.deepCopy();
		for (int row = 0; row < Board.VERTICAL; row++) {
			for (int col = 0; col < Board.HORIZONTAL; col++) {
				assertEquals(
						"For all fields: b.getField(row, col) == copy.getField(row, col)",
						b.getField(row, col), copy.getField(row, col));
			}
		}
	}

	@Test
	public void testEmptyRow() {
		for (int col = 0; col < Board.HORIZONTAL; col++) {
			assertEquals("For all empty columns: b.emptyRow(col) == 5", 5,
					b.emptyRow(col));
		}
		b.insertDisc(2, Disc.YELLOW);
		for (int col = 0; col < Board.HORIZONTAL; col++) {
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
		for (int col = 0; col < Board.HORIZONTAL; col++) {
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
	}

	@Test
	public void testFullRow() {
		for (int col = 0; col < Board.HORIZONTAL; col++) {
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

	@Test
	public void testIsField() {
		// Calling isField(col) with a valid index
		for (int col = 0; col < Board.HORIZONTAL; col++) {
			assertEquals("b.isField(col)", true, b.isField(col));
		}
		// Calling isField(col) with an invalid index

		for (int col = Board.HORIZONTAL; col < Board.HORIZONTAL * 2; col++) {
			assertEquals("For these invalid fields: b.isField(col) == false",
					false, b.isField(col));
		}

		// Calling isField(row, col) with a valid index
		for (int row = 0; row < Board.VERTICAL; row++) {
			for (int col = 0; col < Board.HORIZONTAL; col++) {
				assertEquals(
						"For all valid fields: b.isField(row, col) == true",
						true, b.isField(row, col));
			}
		}
		// Calling isField(row, col) with some invalid indexes
		for (int row = Board.VERTICAL; row < Board.VERTICAL * 2; row++) {
			for (int col = Board.HORIZONTAL; col < Board.HORIZONTAL * 2; col++) {
				assertEquals(
						"For these invalid fields: b.isField(row, col) == false",
						false, b.isField(row, col));
			}
		}
	}

	@Test
	public void testGetField() {
		// Calls all fields, and checks if they're Disc.EMPTY
		for (int row = 0; row < Board.VERTICAL; row++) {
			for (int col = 0; col < Board.HORIZONTAL; col++) {
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
		// Tests some fields outside the board
		for (int row = Board.VERTICAL; row < Board.VERTICAL * 2; row++) {
			for (int col = Board.HORIZONTAL; col < Board.HORIZONTAL * 2; col++) {
				assertEquals(
						"For these invalid fields: b.getField(row, col) == null",
						null, b.getField(row, col));
			}
		}
	}

	@Test
	public void testIsEmptyField() {
		for (int row = 0; row < Board.VERTICAL; row++) {
			for (int col = 0; col < Board.HORIZONTAL; col++) {
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

	@Test
	public void testIsFull() {
		// Puts a random disc on every position of the field. After each
		// placement, a check is made to see that the board is not full yet. At
		// the end, the board should be full.
		for (int row = 0; row < Board.VERTICAL; row++) {
			for (int col = 0; col < Board.HORIZONTAL; col++) {
				if (Math.random() > 0.5) {
					b.setField(row, col, Disc.RED);
				} else {
					b.setField(row, col, Disc.YELLOW);
				}
				if (!(row == Board.VERTICAL - 1 && col == Board.HORIZONTAL - 1)) {
					assertEquals("For a non-full board: b.isFull() == false",
							false, b.isFull());
				} else {
					assertEquals("For a full board: b.isFull() == true", true,
							b.isFull());
				}
			}
		}
	}

	@Test
	public void testIsGameOver() {
		// TODO: Discuss if this method is necessary.
	}

	@Test
	public void testHasRow() {
		// A row is from left to right. At every boardrow, there are 4 potential
		// rows, namely on the positions 0-3, 1-4, 2-5 and 3-6.
		for (int row = 0; row < Board.VERTICAL; row++) {
			// Col <= 3 is hardcoded. In case the Board.HORIZONTAL gets smaller,
			// the Discs can't be changed, and the program will most likely
			// crash. In case the Board.HORIZONTAL is changed to
			// be bigger, this test will not cover all test results.
			for (int col = 0; col <= 3; col++) {
				// Reset the board
				b.reset();
				// Fill the boardrow with a row of 4 discs
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
		// Now tests with rows of 3. For comments, see above code.
		for (int row = 0; row < Board.VERTICAL; row++) {
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
			// TODO: Entend this test with invalid rows.
		}
	}

	@Test
	public void testHasColumn() {
		// A row is from left to right. At every boardrow, there are 3 potential
		// rows, namely on the positions 0-3, 1-4 and 2-5.
		for (int col = 0; col < Board.HORIZONTAL; col++) {
			// Row <= 2 is hardcoded. In case the Board.VERTICAL gets smaller,
			// the Discs can't be changed, and the program will most likely
			// crash. In case the Board.VERTICAL is changed to
			// be bigger, this test will not cover all test results.
			for (int row = 0; row <= 2; row++) {
				// Resets the board
				b.reset();
				// Fill a boardcolumn with a column of 4 discs
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
		// Now tests with columns of 3. For comments, see above code.
		for (int col = 0; col < Board.HORIZONTAL; col++) {
			for (int row = 0; row <= 2; row++) {
				b.reset();
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

	@Test
	public void testHasDiagonal() {
		// TODO: Discuss if this method is necessary.
	}

	@Test
	public void testIsWinner() {
		// TODO: Discuss if this method is necessary.
	}

	@Test
	public void testHasWinner() {
		// TODO: Discuss if this method is necessary.
	}

	@Test
	public void testToString() {
		// TODO: Discuss how to test this.
	}

	@Test
	public void testReset() {
		// Fills the board with Discs
		for (int row = 0; row < Board.VERTICAL; row++) {
			for (int col = 0; col < Board.HORIZONTAL; col++) {
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
		for (int row = 0; row < Board.VERTICAL; row++) {
			for (int col = 0; col < Board.HORIZONTAL; col++) {
				assertEquals("All discs on the board are Disc.EMPTY now.",
						Disc.EMPTY, b.getField(row, col));
			}
		}
	}

	@Test
	public void testInsertDisc() {
		// TODO: Discuss if this method is necessary.
	}

	@Test
	public void testSetField() {
		// TODO: Discuss if this method is necessary.
	}
}