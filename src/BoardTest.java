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
				if (row != Board.VERTICAL && col != Board.HORIZONTAL) {
					if (Math.random() > 0.5) {
						b.setField(row, col, Disc.RED);
					} else {
						b.setField(row, col, Disc.YELLOW);
					}
					assertEquals("For a non-full board: b.isFull() == false",
							false, b.isFull());
				} else {
					assertEquals("For a full board: b.isFull() == true", true,
							b.isFull());
				}

			}
		}
	}
}