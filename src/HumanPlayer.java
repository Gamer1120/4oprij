/**
 * Class for maintaining a human player in Tic Tac Toe.
 * 
 * @author Sven Konings en Michael Koopman
 * @version $Revision: 1.0 $
 */
public class HumanPlayer extends Player {
	/**
	 * View of the game
	 */
	private GameView view;

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
	public HumanPlayer(String name, Disc disc, GameView viewArg) {
		super(name, disc);
		view = viewArg;
	}

	// Commands:

	/*@
		requires board != null;
		ensures board.isField(\result) && board.isEmptyField(\result);
	 */
	/**
	 * Asks the user to input the field where to place the next mark. This is
	 * done using the view.
	 * 
	 * @param board
	 *            the game board
	 * @return the player's chosen field
	 */
	public int determineMove(Board board) {
		int choice = view.makeMove(this);
		boolean valid = board.isField(choice) && board.isEmptyField(choice);
		while (!valid) {
			//TODO: notify invalid move
			choice = view.makeMove(this);
			valid = board.isField(choice) && board.isEmptyField(choice);
		}
		return choice;
	}
}
