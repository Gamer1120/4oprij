package clientserver;

/**
 * ClientView for the Connect4 according to the protocol of the TI-2 group.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public interface ClientView extends MessageUI {

	/**
	 * Asks for the name of the player.
	 */
	public void askName();

	/**
	 * Adds a connect message to the UI.
	 * 
	 * @param message
	 *            The message to add.
	 */
	//@	requires message != null & message.equals("");
	public void addConnectMessage(String message);

	/**
	 * Adds an invite message to the UI.
	 * 
	 * @param message
	 *            The message to add.
	 */
	//@	requires message != null & message.equals("");
	public void addInviteMessage(String message);

	/**
	 * Adds a move message to the UI.
	 * 
	 * @param message
	 *            The message to add.
	 */
	//@	requires message != null & message.equals("");
	public void addMoveMessage(String message);

	/**
	 * Adds a chat message to the UI.
	 * 
	 * @param message
	 *            The message to add.
	 */
	//@	requires message != null & message.equals("");
	public void addChatMessage(String message);

	/**
	 * Adds the board to the UI.
	 */
	public void addBoard();

	/**
	 * Adds a lobby message to the UI.
	 * 
	 * @param message
	 *            The message to add.
	 */
	//@	requires message != null & message.equals("");
	public void addLobbyMessage(String message);

	/**
	 * Adds a leaderboard line message to the UI.
	 * 
	 * @param rank
	 *            The rank this player is.
	 * @param name
	 *            The name of this player.
	 * @param wins
	 *            The amount of wins this player has.
	 * @param losses
	 *            The amount of losses this player has.
	 * @param gamesPlayed
	 *            The amount of games this player has played.
	 */
	/*@	requires rank != null & rank.equals("");
	  	requires name != null & name.equals("");
	  	requires wins != null & wins.equals("");
	  	requires losses != null & losses.equals("");
	  	requires gamesPlayed != null & gamesPlayed.equals("");
	 */
	public void addLeaderBoardLine(String rank, String name, String wins,
			String losses, String gamesPlayed);

	/**
	 * Adds an error message to the UI.
	 * 
	 * @param message
	 *            The message to add.
	 */
	//@	requires message != null & message.equals("");
	public void addErrorMessage(String message);

	/**
	 * Adds a ping message to the UI.
	 * 
	 * @param message
	 *            The message to add.
	 */
	//@	requires message != null & message.equals("");
	public void addPingMessage(String message);

	/**
	 * Adds a help message to the UI.
	 * 
	 * @param message
	 *            The message to add.
	 */
	//@	requires message != null & message.equals("");
	public void addHelpMessage(String message);

	/**
	 * Adds a hint message to the UI.
	 * 
	 * @param move
	 *            The move to add.
	 */
	public void addHintMessage(int move);

	/**
	 * Adds a features message to the UI.
	 * 
	 * @param message
	 *            The message to add.
	 */
	//@	requires message != null & message.equals("");
	public void addFeaturesMessage(String message);

	/**
	 * Adds a game message to the UI.
	 * 
	 * @param message
	 *            The message to add.
	 */
	//@	requires message != null & message.equals("");
	public void addGameMessage(String message);

	/**
	 * Adds a difficulty message to the UI.
	 * 
	 * @param success
	 *            If the change of difficulty was successfull.
	 */
	public void addDifficultyMessage(boolean success);
}
