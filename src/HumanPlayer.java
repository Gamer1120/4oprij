import java.util.Scanner;

/**
 * Class for maintaining a human player in Tic Tac Toe.
 * 
 * @author Sven Konings en Michael Koopman
 * @version $Revision: 1.0 $
 */
public class HumanPlayer extends Player {

	// Constructors:
	/*@
		requires name != null;
		requires mark == Mark.XX || mark == Mark.OO;
		ensures this.getName() == name;
		ensures this.getMark() == mark;
	 */
	/**
	 * Creates a new human player object.
	 */
	public HumanPlayer(String name, Disc disc) {
		super(name, disc);
	}

	// -- Commands ---------------------------------------------------

	/*@
		requires board != null;
		ensures board.isField(\result) && board.isEmptyField(\result);
	 */
	/**
	 * Asks the user to input the field where to place the next mark. This is
	 * done using the standard input/output. \
	 * 
	 * @param board
	 *            the game board
	 * @return the player's chosen field
	 */
	public int determineMove(Board board) {
		String prompt = "> " + getName() + " (" + getDisc().toString() + ")"
				+ ", what is your choice? ";
		int choice = readInt(prompt);
		boolean valid = board.isField(choice) && board.isEmptyField(choice);
		while (!valid) {
			System.out.println("ERROR: field " + choice
					+ " is no valid choice.");
			choice = readInt(prompt);
			valid = board.isField(choice) && board.isEmptyField(choice);
		}
		return choice;
	}

	/**
	 * Writes a prompt to standard out and tries to read an int value from
	 * standard in. This is repeated until an int value is entered.
	 * 
	 * @param prompt
	 *            the question to prompt the user
	 * @return the first int value which is entered by the user
	 */

	@SuppressWarnings("resource")
	private int readInt(String prompt) {
		int value = 0;
		boolean intRead = false;
		do {
			System.out.print(prompt);
			String line = (new Scanner(System.in).nextLine());
			Scanner scannerLine = new Scanner(line);
			if (scannerLine.hasNextInt()) {
				intRead = true;
				value = scannerLine.nextInt();
			}
		} while (!intRead);

		return value;
	}

}
