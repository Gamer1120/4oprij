package clientserver;

import game.Board;
import game.Disc;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;

/**
 * Client program for the Connect4 according to the protocol of the TI-2 group.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public class Client extends Thread {
	// The protocol, as discussed in our TI-2 group. For further explanation,
	// you can look at the protocol documentation.
	public static final String CONNECT = "CONNECT";
	public static final String QUIT = "QUIT";
	public static final String INVITE = "INVITE";
	public static final String ACCEPT_INVITE = "ACCEPT";
	public static final String DECLINE_INVITE = "DECLINE";
	public static final String MOVE = "MOVE";
	public static final String CHAT = "CHAT";
	public static final String REQUEST_BOARD = "REQUEST";
	public static final String REQUEST_LOBBY = "LOBBY";
	public static final String REQUEST_LEADERBOARD = "LEADERBOARD";
	public static final int FIRST_PLAYER = 0;
	public static final int SECOND_PLAYER = 1;
	// END OF PROTOCOL

	/**
	 * The name of this <code>Client</code>.
	 */
	private String clientName;
	/**
	 * The User Interface of this <code>Client</code>.
	 */
	private MessageUI mui;
	/**
	 * The <code>Socket</code> of this <code>Client</code>.
	 */
	private Socket sock;
	/**
	 * The <code>BufferedReader</code> that will be used to communicate over the
	 * <code>Socket</code>.
	 */
	private BufferedReader in;
	/**
	 * The <code>BufferedWriter</code> that will be used to communicate over the
	 * <code>Socket</code>.
	 */
	private BufferedWriter out;
	/**
	 * While this boolean is true, it makes sure that commands are continuously
	 * read from the <code>BufferedReader</code>.
	 */
	private boolean loop;
	/**
	 * A variable to test if a <code>Player</code> is in-game. If they are, they
	 * won't receive any invite messages.
	 */
	private boolean isIngame;
	/**
	 * An <code>ArrayList</code> in which all the invites that are sent by this
	 * client are kept.
	 */
	private ArrayList<String> invites;
	/**
	 * The <code>Board</code> this <code>Client</code> uses for determining
	 * their move.
	 */
	private Board board;
	/**
	 * An integer to determine which <code>Player</code>'s turn it is.
	 */
	private int currPlayer;

	/**
	 * Constructs a <code>Client</code> object and tries to make a
	 * <code>Socket</code> connection
	 * 
	 * @param name
	 *            The name of this <code>Client</code> object.
	 * @param host
	 *            The IP-adress of this <code>Client</code>
	 * @param port
	 *            The port of this <code>Client</code>
	 * @param muiArg
	 *            The <code>MessageUI</code> for this <code>Client</code>
	 */
	public Client(String name, InetAddress host, int port, MessageUI muiArg)
			throws IOException {
		this.clientName = name;
		this.sock = new Socket(host, port);
		this.mui = muiArg;
		this.in = new BufferedReader(new InputStreamReader(
				sock.getInputStream()));
		this.out = new BufferedWriter(new OutputStreamWriter(
				sock.getOutputStream()));
		this.loop = true;
		this.isIngame = false;
		this.invites = new ArrayList<String>();
		mui.addMessage("Your name is: " + name);
	}

	/**
	 * This method reads the messages in the InputStream. Then, it decides which
	 * command was sent, and executes this command by calling the method created
	 * for it.
	 */
	public void run() {
		// TODO: naam vragen inlpaats bij arguments
		// TODO: bij error nog een keer proberen met andere naam
		sendMessage(CONNECT + " " + getClientName());
		while (loop) {
			String line = "";
			try {
				line = in.readLine();
			} catch (IOException | NullPointerException e) {
				shutdown();
			}
			mui.addMessage("Server: " + line);
			String[] serverMessage = line.split("\\s+");
			switch (serverMessage[0]) {
			case Server.ACCEPT_CONNECT:
				connect(serverMessage);
				break;
			case Server.LOBBY:
				lobby(serverMessage);
				break;
			case Server.INVITE:
				invite(serverMessage);
				break;
			case Server.GAME_START:
				gameStart(serverMessage);
				break;
			case Server.GAME_END:
				gameEnd(serverMessage);
				break;
			case Server.REQUEST_MOVE:
				requestMove(serverMessage);
				break;
			case Server.MOVE_OK:
				moveOK(serverMessage);
				break;
			case Server.ERROR:
				error(line);
				break;
			}

		}
	}

	/**
	 * This method accepts the <code>Server.CONNECT</code> packet sent by the
	 * <code>Server</code>. When this method is called, it prints that a
	 * connection has been established with the <code>Server</code>, as well as
	 * the IP adress and port of the <code>Server</code>. After this, it lists
	 * the features the <code>Server</code> has.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	private void connect(String[] serverMessage) {
		mui.addMessage("Successfully established connection to server: "
				+ sock.getRemoteSocketAddress().toString() // IP of
															// the
															// server
				+ ":" + sock.getPort()); // Port of the server
		String listOfFeatures = "";
		for (int i = 1; i < serverMessage.length; i++) {
			listOfFeatures += " " + serverMessage[i];
		}
		mui.addMessage("The features of this server are:" + listOfFeatures);
	}

	/**
	 * This method accepts the <code>Server.LOBBY</code> packet sent by the
	 * <code>Server</code>. When this method is called, it shows the
	 * <code>Client</code> the other <code>Client</code>s that are currently in
	 * the lobby.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	private void lobby(String[] serverMessage) {
		mui.addMessage("The people that are currently in the lobby are:");
		String listOfPeople = "";
		for (int i = 1; i < serverMessage.length; i++) {
			listOfPeople += " " + serverMessage[i];
		}
		mui.addMessage(listOfPeople);
	}

	/**
	 * This method accepts the <code>Server.INVITE</code> packet sent by the
	 * <code>Server</code>. When this method is called, it adds the inviter to
	 * an inviterlist, and, if the player isn't ingame, it will also show the
	 * <code>Client</code> that they have been invited by that
	 * <code>Client</code>.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	private void invite(String[] serverMessage) {
		String opponentName = serverMessage[1];
		invites.add(opponentName);
		if (!isIngame) {
			mui.addMessage("Player: " + opponentName
					+ " has invited you to a game of Connect4!");
		}
	}

	/**
	 * This method accepts the <code>Server.GAME_START</code> packet sent by the
	 * <code>Server</code>. When this method is called, it will show the
	 * <code>Client</code> that a the game is started. The <code>Client</code>
	 * is set to being in-game, and a new <code>Board</code> is created.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	private void gameStart(String[] serverMessage) {
		mui.addMessage("A game between you and " + serverMessage[2]
				+ " has started!");
		this.isIngame = true;
		currPlayer = -1; // Not set yet.
		// DEFINITION: currPlayer == 0 > Disc.YELLOW, currPlayer ==
		// 1 > Disc.RED
		// TODO: board size
		board = new Board();
	}

	/**
	 * This method accepts the <code>Server.GAME_END</code> packet sent by the
	 * <code>Server</code>. When this method is called, it will set the
	 * <code>Client</code> to no longer being in-game.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	private void gameEnd(String[] serverMessage) {
		this.isIngame = false;
		// TODO: Maybe add something here? IDKLOL.
	}

	/**
	 * This method accepts the <code>Server.MOVE</code> packet sent by the
	 * <code>Server</code>. When this method is called, it will request a move
	 * from the <code>Player</code>.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	private void requestMove(String[] serverMessage) {
		if (currPlayer == -1) {
			currPlayer = FIRST_PLAYER;
		}
		// TODO: Actually request a move
	}

	/**
	 * This method accepts the <code>Server.MOVE_OK</code> packet sent by the
	 * <code>Server</code>. When this method is called, it will update the
	 * <code>Board</code> by inserting the <code>Disc</code> for the
	 * <code>Player</code> that was given in the packet.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	private void moveOK(String[] serverMessage) {
		if (currPlayer == -1) {
			currPlayer = SECOND_PLAYER;
		}
		int move = -1;
		// TODO: if else?
		// TODO: checken of move ook kan in bord
		// TODO: betere error handing met request bord
		// TODO: board printen op clientTUI
		switch (currPlayer) {
		case FIRST_PLAYER:
			try {
				move = Integer.parseInt(serverMessage[2]);
			} catch (NumberFormatException e) {
				mui.addMessage("Server did not send a valid move. TERMINATING.");
				shutdown();
			}
			board.insertDisc(move, Disc.YELLOW);
			break;
		case SECOND_PLAYER:
			try {
				move = Integer.parseInt(serverMessage[2]);
			} catch (NumberFormatException e) {
				mui.addMessage("Server did not send a valid move. TERMINATING.");
				shutdown();
			}
			board.insertDisc(move, Disc.RED);
			break;
		}
	}

	/**
	 * This method accepts the <code>Server.ERROR</code> packet sent by the
	 * <code>Server</code>. When this method is called, it shows the
	 * <code>Client</code> the error.
	 * 
	 * @param line
	 *            The raw error the server sent.
	 */
	private void error(String line) {
		mui.addMessage(line);
	}

	/**
	 * This method sends a message to the <code>ClientHandler</code> using the
	 * <code>OutputStream</code> out.
	 * 
	 * @param msg
	 *            The message to be sent.
	 */
	public void sendMessage(String msg) {
		try {
			out.write(msg);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			shutdown();
		}
	}

	/**
	 * This method closes the <code>Socket</code> connection and exits the
	 * program. On a side note, before it does this, it also sets the loop and
	 * isIngame variables for this <code>Client</code> to false.
	 */
	public void shutdown() {
		loop = false;
		isIngame = false;
		try {
			sock.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		System.exit(0);
	}

	/**
	 * This method returns the name of this <code>Client</code>.
	 */
	public String getClientName() {
		return clientName;
	}

} // end of class Client
