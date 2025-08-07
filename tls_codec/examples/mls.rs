use std::io::{Read, Write};

use tls_codec::{
    Deserialize, DeserializeBytes, Error, SecretVLBytes, Serialize, Size, TlsDeserialize,
    TlsDeserializeBytes, TlsSerialize, TlsSerializeBytes, TlsSize, VLBytes,
};

// uint16 CipherSuite;
#[derive(
    PartialEq,
    Debug,
    Clone,
    TlsSerialize,
    TlsDeserialize,
    TlsSerializeBytes,
    TlsDeserializeBytes,
    TlsSize,
)]
struct Ciphersuite(u16);

// enum {
//   reserved(0),
//   external(1),
//   resumption(2),
//   (255)
// } PSKType;
#[derive(
    Clone,
    Copy,
    Debug,
    Eq,
    PartialEq,
    TlsSerialize,
    TlsDeserialize,
    TlsSerializeBytes,
    TlsDeserializeBytes,
    TlsSize,
)]
#[repr(u8)]
pub enum PskType {
    /// An external PSK.
    External = 1,
    /// A resumption PSK.
    Resumption = 2,
}

/// External PSK.
#[derive(
    Debug,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Clone,
    Hash,
    TlsDeserialize,
    TlsDeserializeBytes,
    TlsSerialize,
    TlsSize,
)]
pub struct ExternalPsk {
    psk_id: VLBytes,
}

#[derive(
    Clone,
    Copy,
    Debug,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    TlsDeserialize,
    TlsSerializeBytes,
    TlsDeserializeBytes,
    TlsSerialize,
    TlsSize,
)]
pub struct GroupEpoch(u64);

#[derive(
    Clone,
    Debug,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    TlsDeserialize,
    TlsDeserializeBytes,
    TlsSerialize,
    TlsSize,
)]
pub struct ResumptionPsk {
    pub(crate) usage: ResumptionPskUsage,
    pub(crate) psk_group_id: VLBytes,
    pub(crate) psk_epoch: GroupEpoch,
}

#[derive(
    Clone,
    Debug,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    TlsDeserialize,
    TlsDeserializeBytes,
    TlsSerialize,
    TlsSize,
)]
#[repr(u8)]
pub enum Psk {
    /// An external PSK provided by the application.
    #[tls_codec(discriminant = 1)]
    External(ExternalPsk),
    /// A resumption PSK derived from the MLS key schedule.
    #[tls_codec(discriminant = 2)]
    Resumption(ResumptionPsk),
}

// enum {
//   reserved(0),
//   application(1),
//   reinit(2),
//   branch(3),
//   (255)
// } ResumptionPSKUsage;

#[derive(
    Clone,
    Copy,
    Debug,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    TlsDeserialize,
    TlsSerializeBytes,
    TlsDeserializeBytes,
    TlsSerialize,
    TlsSize,
)]
#[repr(u8)]
pub enum ResumptionPskUsage {
    /// Application.
    Application = 1,
    /// Resumption PSK used for group reinitialization.
    ///
    /// Note: "Resumption PSKs with usage `reinit` MUST NOT be used in other contexts (than reinitialization)."
    Reinit = 2,
    /// Resumption PSK used for subgroup branching.
    ///
    /// Note: "Resumption PSKs with usage `branch` MUST NOT be used in other contexts (than subgroup branching)."
    Branch = 3,
}

// struct {
//   PSKType psktype;
//   select (PreSharedKeyID.psktype) {
//     case external:
//       opaque psk_id<V>;

//     case resumption:
//       ResumptionPSKUsage usage;
//       opaque psk_group_id<V>;
//       uint64 psk_epoch;
//   };
//   opaque psk_nonce<V>;
// } PreSharedKeyID;

#[derive(
    Clone,
    Debug,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    TlsDeserialize,
    TlsDeserializeBytes,
    TlsSerialize,
    TlsSize,
)]
pub struct PreSharedKeyId {
    pub(crate) psk: Psk,
    pub(crate) psk_nonce: VLBytes,
}

// struct {
//   opaque path_secret<V>;
// } PathSecret;

#[derive(Clone, TlsSerialize, TlsDeserialize, TlsDeserializeBytes, TlsSize)]
pub(crate) struct Secret {
    value: SecretVLBytes,
}

#[derive(TlsSerialize, TlsDeserialize, TlsDeserializeBytes, TlsSize)]
pub(crate) struct PathSecret {
    path_secret: Secret,
}

// struct {
//   opaque joiner_secret<V>;
//   optional<PathSecret> path_secret;
//   PreSharedKeyID psks<V>;
// } GroupSecrets;

#[derive(TlsDeserialize, TlsDeserializeBytes, TlsSerialize, TlsSize)]
pub(crate) struct JoinerSecret {
    secret: Secret,
}

#[derive(TlsSerialize, TlsDeserialize, TlsDeserializeBytes, TlsSize)]
pub(crate) struct GroupSecrets {
    pub(crate) joiner_secret: JoinerSecret,
    pub(crate) path_secret: Option<PathSecret>,
    pub(crate) psks: Vec<PreSharedKeyId>,
}

// struct {
//   KeyPackageRef new_member;
//   HPKECiphertext encrypted_group_secrets;
// } EncryptedGroupSecrets;

#[derive(
    Clone,
    Debug,
    Hash,
    PartialEq,
    Eq,
    Ord,
    PartialOrd,
    TlsDeserialize,
    TlsDeserializeBytes,
    TlsSerialize,
    TlsSize,
)]
pub struct HashReference {
    value: VLBytes,
}

pub type KeyPackageRef = HashReference;

#[derive(Debug, TlsSerialize, TlsDeserialize, TlsDeserializeBytes, TlsSize)]
pub struct HpkeCiphertext {
    pub kem_output: VLBytes,
    pub ciphertext: VLBytes,
}

#[derive(Debug, TlsDeserialize, TlsDeserializeBytes, TlsSerialize, TlsSize)]
pub struct EncryptedGroupSecrets {
    /// Key package reference of the new member
    new_member: KeyPackageRef,
    /// Ciphertext of the encrypted group secret
    encrypted_group_secrets: HpkeCiphertext,
}

// struct {
//   CipherSuite cipher_suite;
//   EncryptedGroupSecrets secrets<V>;
//   opaque encrypted_group_info<V>;
// } Welcome;

#[derive(TlsDeserialize, TlsDeserializeBytes, TlsSerialize, TlsSize)]
pub struct Welcome {
    cipher_suite: Ciphersuite,
    secrets: Vec<EncryptedGroupSecrets>,
    encrypted_group_info: VLBytes,
}

// enum {
//     reserved(0),
//     mls10(1),
//     (65535)
// } ProtocolVersion;
#[derive(
    Debug,
    Copy,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    TlsDeserialize,
    TlsDeserializeBytes,
    TlsSerialize,
    TlsSize,
)]
#[repr(u16)]
pub enum ProtocolVersion {
    Mls10 = 1,
    Other(u16),
}

// enum {
//     reserved(0),
//     application(1),
//     proposal(2),
//     commit(3),
//     (255)
// } ContentType;

#[derive(
    PartialEq, Eq, Clone, Copy, Debug, TlsDeserialize, TlsDeserializeBytes, TlsSerialize, TlsSize,
)]
#[repr(u8)]
pub enum ContentType {
    /// Application message
    Application = 1,
    /// Proposal
    Proposal = 2,
    /// Commit
    Commit = 3,
}

// enum {
//     reserved(0),
//     member(1),
//     external(2),
//     new_member_proposal(3),
//     new_member_commit(4),
//     (255)
// } SenderType;

// struct {
//     SenderType sender_type;
//     select (Sender.sender_type) {
//         case member:
//             uint32 leaf_index;
//         case external:
//             uint32 sender_index;
//         case new_member_commit:
//         case new_member_proposal:
//             struct{};
//     };
// } Sender;

#[derive(
    Debug,
    Clone,
    Copy,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    TlsDeserialize,
    TlsDeserializeBytes,
    TlsSerialize,
    TlsSize,
)]
pub struct LeafNodeIndex(u32);
#[derive(
    Debug,
    Clone,
    Copy,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    TlsDeserialize,
    TlsDeserializeBytes,
    TlsSerialize,
    TlsSize,
)]
pub struct SenderExtensionIndex(u32);

#[derive(
    Debug, PartialEq, Eq, Clone, TlsSerialize, TlsDeserialize, TlsDeserializeBytes, TlsSize,
)]
#[repr(u8)]
pub enum Sender {
    /// The sender is a member of the group
    #[tls_codec(discriminant = 1)]
    Member(LeafNodeIndex),
    /// The sender is not a member of the group and has an external value instead
    /// The index refers to the [crate::extensions::ExternalSendersExtension] and is 0 indexed
    External(SenderExtensionIndex),
    /// The sender is a new member of the group that joins itself through
    /// an [External Add proposal](crate::messages::external_proposals::JoinProposal)
    NewMemberProposal,
    /// The sender is a new member of the group that joins itself through
    /// an [External Commit](crate::group::mls_group::MlsGroup::external_commit_builder)
    NewMemberCommit,
}

// uint16 WireFormat;
#[derive(
    PartialEq, Eq, Clone, Copy, Debug, TlsDeserialize, TlsDeserializeBytes, TlsSerialize, TlsSize,
)]
#[repr(u16)]
pub enum WireFormat {
    /// Plaintext message
    PublicMessage = 1,
    /// Encrypted message
    PrivateMessage = 2,
    /// Welcome message
    Welcome = 3,
    /// Group information
    GroupInfo = 4,
    /// KeyPackage
    KeyPackage = 5,
}

// struct {
//     opaque group_id<V>;
//     uint64 epoch;
//     Sender sender;
//     opaque authenticated_data<V>;

//     ContentType content_type;
//     select (FramedContent.content_type) {
//         case application:
//           opaque application_data<V>;
//         case proposal:
//           Proposal proposal;
//         case commit:
//           Commit commit;
//     };
// } FramedContent;

#[derive(Debug, Clone, PartialEq, TlsSize, TlsSerialize, TlsDeserialize, TlsDeserializeBytes)]
pub struct InitKey {
    key: VLBytes,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u16)]
pub enum CredentialType {
    /// A [`BasicCredential`]
    Basic = 1,
    /// An X.509 [`Certificate`]
    X509 = 2,
    /// Another type of credential that is not in the MLS protocol spec.
    Other(u16),
}

impl From<u16> for CredentialType {
    fn from(value: u16) -> Self {
        match value {
            1 => CredentialType::Basic,
            2 => CredentialType::X509,
            other => CredentialType::Other(other),
        }
    }
}

impl From<CredentialType> for u16 {
    fn from(value: CredentialType) -> Self {
        match value {
            CredentialType::Basic => 1,
            CredentialType::X509 => 2,
            CredentialType::Other(other) => other,
        }
    }
}

impl Size for CredentialType {
    fn tls_serialized_len(&self) -> usize {
        2
    }
}

impl Deserialize for CredentialType {
    fn tls_deserialize<R: Read>(bytes: &mut R) -> Result<Self, Error>
    where
        Self: Sized,
    {
        let mut extension_type = [0u8; 2];
        bytes.read_exact(&mut extension_type)?;

        Ok(CredentialType::from(u16::from_be_bytes(extension_type)))
    }
}

impl Serialize for CredentialType {
    fn tls_serialize<W: Write>(&self, writer: &mut W) -> Result<usize, Error> {
        writer.write_all(&u16::from(*self).to_be_bytes()).unwrap();

        Ok(2)
    }
}

impl DeserializeBytes for CredentialType {
    fn tls_deserialize_bytes(bytes: &[u8]) -> Result<(Self, &[u8]), Error>
    where
        Self: Sized,
    {
        let mut bytes_ref = bytes;
        let credential_type = CredentialType::tls_deserialize(&mut bytes_ref).unwrap();
        let remainder = &bytes[credential_type.tls_serialized_len()..];
        Ok((credential_type, remainder))
    }
}

#[derive(
    Debug, PartialEq, Eq, Clone, TlsSize, TlsSerialize, TlsDeserialize, TlsDeserializeBytes,
)]
pub struct Credential {
    credential_type: CredentialType,
    serialized_credential_content: VLBytes,
}

#[derive(
    Debug,
    Copy,
    Clone,
    PartialEq,
    Eq,
    Hash,
    Ord,
    PartialOrd,
    TlsSerialize,
    TlsDeserialize,
    TlsDeserializeBytes,
    TlsSize,
)]
#[repr(u16)]
pub enum ExtensionType {
    /// The application id extension allows applications to add an explicit,
    /// application-defined identifier to a KeyPackage.
    ApplicationId,

    /// The ratchet tree extensions provides the whole public state of the
    /// ratchet tree.
    RatchetTree,

    /// The required capabilities extension defines the configuration of a group
    /// that imposes certain requirements on clients in the group.
    RequiredCapabilities,

    /// To join a group via an External Commit, a new member needs a GroupInfo
    /// with an ExternalPub extension present in its extensions field.
    ExternalPub,

    /// Group context extension that contains the credentials and signature keys
    /// of senders that are permitted to send external proposals to the group.
    ExternalSenders,

    /// KeyPackage extension that marks a KeyPackage for use in a last resort
    /// scenario.
    LastResort,

    /// A currently unknown extension type.
    Unknown(u16),
}

#[derive(
    Debug, Clone, PartialEq, Eq, TlsSerialize, TlsDeserialize, TlsDeserializeBytes, TlsSize,
)]
pub struct Capabilities {
    versions: Vec<ProtocolVersion>,
    ciphersuites: Vec<u16>,
    extensions: Vec<ExtensionType>,
    credentials: Vec<CredentialType>,
}

#[derive(
    PartialEq, Eq, Copy, Clone, Debug, TlsSerialize, TlsSize, TlsDeserialize, TlsDeserializeBytes,
)]
pub struct Lifetime {
    not_before: u64,
    not_after: u64,
}

#[derive(
    Debug, Clone, PartialEq, Eq, TlsSerialize, TlsDeserialize, TlsDeserializeBytes, TlsSize,
)]
#[repr(u8)]
pub enum LeafNodeSource {
    /// The leaf node was added to the group as part of a key package.
    #[tls_codec(discriminant = 1)]
    KeyPackage(Lifetime),
    /// The leaf node was added through an Update proposal.
    Update,
    /// The leaf node was added via a Commit.
    Commit(VLBytes),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Extension {
    /// An [`ApplicationIdExtension`]
    ApplicationId(VLBytes),
    // ...
}

impl Extension {
    pub const fn extension_type(&self) -> ExtensionType {
        match self {
            Extension::ApplicationId(_) => ExtensionType::ApplicationId,
        }
    }
}

impl Size for Extension {
    #[inline]
    fn tls_serialized_len(&self) -> usize {
        let extension_type_length = 2;

        // We truncate here and don't catch errors for anything that's
        // too long.
        // This will be caught when (de)serializing.
        let extension_data_len = match self {
            Extension::ApplicationId(e) => e.tls_serialized_len(),
        };

        let vlbytes_len_len = vlbytes_len_len(extension_data_len);

        extension_type_length + vlbytes_len_len + extension_data_len
    }
}

impl Size for &Extension {
    #[inline]
    fn tls_serialized_len(&self) -> usize {
        Extension::tls_serialized_len(*self)
    }
}

fn vlbytes_len_len(length: usize) -> usize {
    if length < 0x40 {
        1
    } else if length < 0x3fff {
        2
    } else if length < 0x3fff_ffff {
        4
    } else {
        8
    }
}

impl Serialize for Extension {
    fn tls_serialize<W: Write>(&self, writer: &mut W) -> Result<usize, tls_codec::Error> {
        // First write the extension type.
        let written = self.extension_type().tls_serialize(writer)?;

        // Now serialize the extension into a separate byte vector.
        let extension_data_len = self.tls_serialized_len();
        let mut extension_data = Vec::with_capacity(extension_data_len);

        let extension_data_written = match self {
            Extension::ApplicationId(e) => e.tls_serialize(&mut extension_data),
        }?;
        debug_assert_eq!(
            extension_data_written,
            extension_data_len - 2 - vlbytes_len_len(extension_data_written)
        );
        debug_assert_eq!(extension_data_written, extension_data.len());

        // Write the serialized extension out.
        extension_data.tls_serialize(writer).map(|l| l + written)
    }
}

impl Serialize for &Extension {
    fn tls_serialize<W: Write>(&self, writer: &mut W) -> Result<usize, tls_codec::Error> {
        Extension::tls_serialize(*self, writer)
    }
}

impl Deserialize for Extension {
    fn tls_deserialize<R: Read>(bytes: &mut R) -> Result<Self, tls_codec::Error> {
        // Read the extension type and extension data.
        let extension_type = ExtensionType::tls_deserialize(bytes)?;
        let extension_data = VLBytes::tls_deserialize(bytes)?;

        // Now deserialize the extension itself from the extension data.
        let mut extension_data = extension_data.as_slice();
        Ok(match extension_type {
            ExtensionType::ApplicationId => {
                Extension::ApplicationId(VLBytes::tls_deserialize(&mut extension_data)?)
            }
            _ => unimplemented!(),
        })
    }
}

impl DeserializeBytes for Extension {
    fn tls_deserialize_bytes(bytes: &[u8]) -> Result<(Self, &[u8]), tls_codec::Error>
    where
        Self: Sized,
    {
        let mut bytes_ref = bytes;
        let extension = Extension::tls_deserialize(&mut bytes_ref)?;
        let remainder = &bytes[extension.tls_serialized_len()..];
        Ok((extension, remainder))
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq, TlsSize)]
pub struct Extensions {
    unique: Vec<Extension>,
}

impl Serialize for Extensions {
    fn tls_serialize<W: Write>(&self, writer: &mut W) -> Result<usize, Error> {
        self.unique.tls_serialize(writer)
    }
}

impl TryFrom<Vec<Extension>> for Extensions {
    type Error = u8;

    fn try_from(candidate: Vec<Extension>) -> Result<Self, Self::Error> {
        let mut unique: Vec<Extension> = Vec::new();

        for extension in candidate.into_iter() {
            if unique
                .iter()
                .any(|ext| ext.extension_type() == extension.extension_type())
            {
                return Err(1);
            } else {
                unique.push(extension);
            }
        }

        Ok(Self { unique })
    }
}

impl Deserialize for Extensions {
    fn tls_deserialize<R: Read>(bytes: &mut R) -> Result<Self, Error>
    where
        Self: Sized,
    {
        let candidate: Vec<Extension> = Vec::tls_deserialize(bytes)?;
        Extensions::try_from(candidate)
            .map_err(|_| Error::DecodingError("Found duplicate extensions".into()))
    }
}

impl DeserializeBytes for Extensions {
    fn tls_deserialize_bytes(bytes: &[u8]) -> Result<(Self, &[u8]), Error>
    where
        Self: Sized,
    {
        let mut bytes_ref = bytes;
        let extensions = Extensions::tls_deserialize(&mut bytes_ref)?;
        let remainder = &bytes[extensions.tls_serialized_len()..];
        Ok((extensions, remainder))
    }
}

#[derive(
    Debug, Clone, PartialEq, Eq, TlsSerialize, TlsDeserialize, TlsDeserializeBytes, TlsSize,
)]
struct LeafNodePayload {
    encryption_key: VLBytes,
    signature_key: VLBytes,
    credential: Credential,
    capabilities: Capabilities,
    leaf_node_source: LeafNodeSource,
    extensions: Extensions,
}

#[derive(Debug, Clone, PartialEq, Eq, TlsSerialize, TlsSize)]
pub struct LeafNode {
    payload: LeafNodePayload,
    signature: VLBytes,
}

#[derive(PartialEq, Debug, Clone, TlsSize, TlsSerialize)]
struct KeyPackageTbs {
    protocol_version: ProtocolVersion,
    ciphersuite: Ciphersuite,
    init_key: InitKey,
    leaf_node: LeafNode,
    extensions: Extensions,
}

#[derive(PartialEq, Debug, Clone, TlsSize, TlsSerialize)]
pub struct KeyPackage {
    payload: KeyPackageTbs,
    signature: VLBytes,
}

#[derive(Debug, PartialEq, Clone, TlsSerialize, TlsSize)]
pub struct AddProposal {
    pub(crate) key_package: KeyPackage,
}

#[derive(Debug, PartialEq, Clone)]
#[repr(u16)]
pub enum Proposal {
    Add(AddProposal),
    // ...
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash, TlsSize, TlsSerialize)]
#[repr(u16)]
pub enum ProposalType {
    Add,
    Update,
    Remove,
    PreSharedKey,
    Reinit,
    ExternalInit,
    GroupContextExtensions,
    AppAck,
    SelfRemove,
    Custom(u16),
}

impl Proposal {
    pub fn proposal_type(&self) -> ProposalType {
        match self {
            Proposal::Add(_) => ProposalType::Add,
        }
    }
}

impl Size for Proposal {
    fn tls_serialized_len(&self) -> usize {
        self.proposal_type().tls_serialized_len()
            + match self {
                Proposal::Add(p) => p.tls_serialized_len(),
            }
    }
}

impl Serialize for Proposal {
    fn tls_serialize<W: std::io::Write>(&self, writer: &mut W) -> Result<usize, tls_codec::Error> {
        let written = self.proposal_type().tls_serialize(writer)?;
        match self {
            Proposal::Add(p) => p.tls_serialize(writer),
        }
        .map(|l| written + l)
    }
}

#[derive(Debug, PartialEq, Clone, TlsSerialize, TlsSize)]
#[repr(u8)]
pub enum FramedContentBody {
    #[tls_codec(discriminant = 1)]
    Application(VLBytes),
    #[tls_codec(discriminant = 2)]
    Proposal(Proposal),
    // #[tls_codec(discriminant = 3)]
    // Commit(Commit),
}

#[derive(Debug, PartialEq, Clone, TlsSerialize, TlsSize)]
pub struct FramedContent {
    pub group_id: VLBytes,
    pub epoch: GroupEpoch,
    pub sender: Sender,
    pub authenticated_data: VLBytes,
    pub body: FramedContentBody,
}

// struct {
//     ProtocolVersion version = mls10;
//     WireFormat wire_format;
//     select (MLSMessage.wire_format) {
//         case mls_public_message:
//             PublicMessage public_message;
//         case mls_private_message:
//             PrivateMessage private_message;
//         case mls_welcome:
//             Welcome welcome;
//         case mls_group_info:
//             GroupInfo group_info;
//         case mls_key_package:
//             KeyPackage key_package;
//     };
// } MLSMessage;

// struct {
//     WireFormat wire_format;
//     FramedContent content;
//     FramedContentAuthData auth;
// } AuthenticatedContent;

// struct {
//     ProtocolVersion version = mls10;
//     WireFormat wire_format;
//     FramedContent content;
//     select (FramedContentTBS.content.sender.sender_type) {
//         case member:
//         case new_member_commit:
//             GroupContext context;
//         case external:
//         case new_member_proposal:
//             struct{};
//     };
// } FramedContentTBS;

#[derive(PartialEq, Debug, Clone)]
pub(crate) struct FramedContentAuthData {
    pub signature: VLBytes,
    pub confirmation_tag: Option<VLBytes>,
}

impl Size for FramedContentAuthData {
    #[inline]
    fn tls_serialized_len(&self) -> usize {
        self.signature.tls_serialized_len()
            + if let Some(confirmation_tag) = &self.confirmation_tag {
                confirmation_tag.tls_serialized_len()
            } else {
                0
            }
    }
}

impl Serialize for FramedContentAuthData {
    fn tls_serialize<W: Write>(&self, writer: &mut W) -> Result<usize, tls_codec::Error> {
        let mut written = self.signature.tls_serialize(writer)?;
        written += if let Some(confirmation_tag) = &self.confirmation_tag {
            confirmation_tag.tls_serialize(writer)?
        } else {
            0
        };
        Ok(written)
    }
}

#[derive(PartialEq, Debug, Clone, TlsSerialize, TlsSize)]
pub(crate) struct AuthenticatedContent {
    pub wire_format: WireFormat,
    pub content: FramedContent,
    pub auth: FramedContentAuthData,
}

// opaque MAC<V>;

// struct {
//     /* SignWithLabel(., "FramedContentTBS", FramedContentTBS) */
//     opaque signature<V>;
//     select (FramedContent.content_type) {
//         case commit:
//             /*
//               MAC(confirmation_key,
//                   GroupContext.confirmed_transcript_hash)
//             */
//             MAC confirmation_tag;
//         case application:
//         case proposal:
//             struct{};
//     };
// } FramedContentAuthData;

// struct {
//     FramedContent content;
//     FramedContentAuthData auth;
//     select (PublicMessage.content.sender.sender_type) {
//         case member:
//             MAC membership_tag;
//         case external:
//         case new_member_commit:
//         case new_member_proposal:
//             struct{};
//     };
// } PublicMessage;

// struct {
//   FramedContentTBS content_tbs;
//   FramedContentAuthData auth;
// } AuthenticatedContentTBM;

// struct {
//     opaque group_id<V>;
//     uint64 epoch;
//     ContentType content_type;
//     opaque authenticated_data<V>;
//     opaque encrypted_sender_data<V>;
//     opaque ciphertext<V>;
// } PrivateMessage;

// struct {
//     select (PrivateMessage.content_type) {
//         case application:
//           opaque application_data<V>;

//         case proposal:
//           Proposal proposal;

//         case commit:
//           Commit commit;
//     };

//     FramedContentAuthData auth;
//     opaque padding[length_of_padding];
// } PrivateMessageContent;

// struct {
//     opaque group_id<V>;
//     uint64 epoch;
//     ContentType content_type;
//     opaque authenticated_data<V>;
// } PrivateContentAAD;

// struct {
//     uint32 leaf_index;
//     uint32 generation;
//     opaque reuse_guard[4];
// } SenderData;

// struct {
//     opaque group_id<V>;
//     uint64 epoch;
//     ContentType content_type;
// } SenderDataAAD;

// struct {
//     HPKEPublicKey encryption_key;
//     opaque parent_hash<V>;
//     uint32 unmerged_leaves<V>;
// } ParentNode;

// enum {
//     reserved(0),
//     key_package(1),
//     update(2),
//     commit(3),
//     (255)
// } LeafNodeSource;

// struct {
//     ProtocolVersion versions<V>;
//     CipherSuite cipher_suites<V>;
//     ExtensionType extensions<V>;
//     ProposalType proposals<V>;
//     CredentialType credentials<V>;
// } Capabilities;

// struct {
//     uint64 not_before;
//     uint64 not_after;
// } Lifetime;

// uint16 ExtensionType;

// struct {
//     ExtensionType extension_type;
//     opaque extension_data<V>;
// } Extension;

// struct {
//     HPKEPublicKey encryption_key;
//     SignaturePublicKey signature_key;
//     Credential credential;
//     Capabilities capabilities;

//     LeafNodeSource leaf_node_source;
//     select (LeafNode.leaf_node_source) {
//         case key_package:
//             Lifetime lifetime;

//         case update:
//             struct{};

//         case commit:
//             opaque parent_hash<V>;
//     };

//     Extension extensions<V>;
//     /* SignWithLabel(., "LeafNodeTBS", LeafNodeTBS) */
//     opaque signature<V>;
// } LeafNode;

// struct {
//     HPKEPublicKey encryption_key;
//     SignaturePublicKey signature_key;
//     Credential credential;
//     Capabilities capabilities;

//     LeafNodeSource leaf_node_source;
//     select (LeafNodeTBS.leaf_node_source) {
//         case key_package:
//             Lifetime lifetime;

//         case update:
//             struct{};

//         case commit:
//             opaque parent_hash<V>;
//     };

//     Extension extensions<V>;

//     select (LeafNodeTBS.leaf_node_source) {
//         case key_package:
//             struct{};

//         case update:
//             opaque group_id<V>;
//             uint32 leaf_index;

//         case commit:
//             opaque group_id<V>;
//             uint32 leaf_index;
//     };
// } LeafNodeTBS;

fn main() {}
