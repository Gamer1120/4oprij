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
	 * 
	 * @return
	 */
	public void askName();

	public void addConnectMessage(String message);

	public void addInviteMessage(String message);

	public void addMoveMessage(String message);

	public void addChatMessage(String message);

	public void addBoard();

	public void addLobbyMessage(String message);

	public void addLeaderBoardLine(String rank, String name, String wins,
			String losses, String gamesPlayed);

	public void addErrorMessage(String message);

	public void addPingMessage(String message);

	public void addHelpMessage(String message);

	public void addHintMessage(int move);

	public void addFeaturesMessage(String message);

	public void addGameMessage(String message);

	public void addDifficultyMessage(boolean succes);
}
